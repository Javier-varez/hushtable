use std::borrow::Borrow;
use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash};
use std::mem::MaybeUninit;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("The map is full")]
    MapFull,
}

const DEFAULT_SIZE: usize = 1024;

/// An implementation of a HashMap that implements a fast open addressing hash table with linear
/// probing.
///
/// The size is fixed and given by a generic parameter `Size`.
///
/// Note that the internal fields of the map are boxed so that moving a map does not imply a large
/// copy of data. Additionally, this reduces the risk of stack overflow when the maps are large.
pub struct HashMap<K, V, H = BuildHasherDefault<DefaultHasher>, const SIZE: usize = DEFAULT_SIZE>
where
    H: BuildHasher + Default,
{
    inner: Box<HashMapData<K, V, H, SIZE>>,
}

impl<K, V> HashMap<K, V>
where
    K: Hash + Eq,
{
    /// Creates a new empty HashMap with default capacity
    pub fn new() -> HashMap<K, V, BuildHasherDefault<DefaultHasher>, DEFAULT_SIZE> {
        Self::with_hasher_and_capacity::<BuildHasherDefault<DefaultHasher>, DEFAULT_SIZE>()
    }

    /// Creates a new empty HashMap with the given capacity
    pub fn with_capacity<const S: usize>() -> HashMap<K, V, BuildHasherDefault<DefaultHasher>, S> {
        Self::with_hasher_and_capacity::<BuildHasherDefault<DefaultHasher>, S>()
    }

    /// Creates a new empty HashMap with the given hasher and capacity
    pub fn with_hasher_and_capacity<HASHER: BuildHasher + Default, const S: usize>(
    ) -> HashMap<K, V, HASHER, S> {
        HashMap {
            inner: Box::new(HashMapData::with_hasher_and_capacity::<HASHER, S>()),
        }
    }
}

impl<K, V, H, const SIZE: usize> HashMap<K, V, H, SIZE>
where
    K: Hash + Eq,
    H: BuildHasher + Default,
{
    /// Inserts a new key-value pair or replaces a key’s existing value
    pub fn insert(&mut self, key: K, value: V) -> Result<(), Error> {
        self.inner.insert(key, value)
    }

    /// Removes the corresponding key-value pair
    pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Q: Hash + Eq + ?Sized,
        K: Borrow<Q>,
    {
        self.inner.remove(key)
    }

    /// Returns the value of the corresponding key
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        // Q is borrowed so we don't need it to be sized. This gives us better ergonomics with
        // types like `str` and `String`.
        Q: Hash + Eq + ?Sized,
        K: Borrow<Q>,
    {
        self.inner.get(key)
    }

    /// Returns the most recent key-value pair that was either inserted or
    /// updated and is still present,
    pub fn get_last(&self) -> Option<(&K, &V)> {
        self.inner.get_last()
    }

    /// returns the least recent key-value pair that was either inserted or
    /// updated and is still present
    pub fn get_first(&self) -> Option<(&K, &V)> {
        self.inner.get_first()
    }
}

struct HashMapData<K, V, H = BuildHasherDefault<DefaultHasher>, const SIZE: usize = DEFAULT_SIZE>
where
    H: BuildHasher,
{
    // - This could have been a `Vec<MaybeUninit<K>>`, but the boxed array represents better the
    //   semantics of the code.
    // - I used MaybeUninit because the validity semantics are encoded separately in `meta`, so
    //   Option<> would include redundant information.
    // - I chose to have the keys contiguous because linear probing implies that we may need to
    //   compare multiple keys in sequence, so this should give better cache locality and be faster.
    keys: [MaybeUninit<K>; SIZE],
    values: [MaybeUninit<V>; SIZE],

    // A contiguous metadata block should have better cache locality properties when the entry is not
    // found, hopefully allowing faster linear probing.
    // In principle, we could be smart here and compress the metadata and do the lookup using SIMD
    // instructions.
    meta: Meta<SIZE>,
    hasher_builder: H,
}

impl<K, V> HashMapData<K, V>
where
    K: Hash + Eq,
{
    const UNINIT_KEY: MaybeUninit<K> = MaybeUninit::uninit();
    const UNINIT_VALUE: MaybeUninit<V> = MaybeUninit::uninit();

    /// Creates a new empty HashMap with the given hasher and capacity
    fn with_hasher_and_capacity<HASHER: BuildHasher + Default, const S: usize>(
    ) -> HashMapData<K, V, HASHER, S> {
        HashMapData {
            keys: [Self::UNINIT_KEY; S],
            values: [Self::UNINIT_VALUE; S],
            meta: Meta::new(),
            hasher_builder: HASHER::default(),
        }
    }
}

impl<K, V, H, const SIZE: usize> HashMapData<K, V, H, SIZE>
where
    K: Hash + Eq,
    H: BuildHasher + Default,
{
    /// Inserts a new key-value pair or replaces a key’s existing value
    fn insert(&mut self, key: K, value: V) -> Result<(), Error> {
        let hash = self.hasher_builder.hash_one(&key);
        let mut index = (hash as usize) % SIZE;

        for _ in 0..SIZE {
            match self.meta.status[index] {
                Status::Free | Status::Deleted => {
                    self.keys[index].write(key);
                    self.values[index].write(value);
                    self.meta.mark_used(index);
                    return Ok(());
                }
                Status::Used if unsafe { self.key_matches(index, &key) } => {
                    unsafe {
                        // Droping the old key-value pair intentionally, as it has been replaced.
                        let _ = std::mem::replace(self.keys[index].assume_init_mut(), key);
                        let _ = std::mem::replace(self.values[index].assume_init_mut(), value);
                    }
                    self.meta.mark_used(index);
                    return Ok(());
                }
                Status::Used => {
                    // FIXME: The table is full and the key is not present
                    index = (index + 1) % SIZE;
                }
            }
        }

        Err(Error::MapFull)
    }

    /// Removes the corresponding key-value pair
    fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Q: Hash + Eq + ?Sized,
        K: Borrow<Q>,
    {
        let build_hasher = H::default();
        let hash = build_hasher.hash_one(key);
        let mut index = (hash as usize) % SIZE;

        for _ in 0..SIZE {
            match self.meta.status[index] {
                Status::Free => {
                    // The entry is not in the hash map
                    return None;
                }
                Status::Used if unsafe { self.key_matches(index, key) } => {
                    self.meta.mark_removed(index);

                    // SAFETY:
                    //   - We know that both keys[index] and the value taken from values[index]
                    //     were initialized because the status[index] flag was Used.
                    let key = std::mem::replace(&mut self.keys[index], MaybeUninit::uninit());
                    let value = std::mem::replace(&mut self.values[index], MaybeUninit::uninit());
                    unsafe {
                        return Some((key.assume_init(), value.assume_init()));
                    }
                }
                Status::Deleted | Status::Used => {
                    // FIXME: The table is full and the key is not present
                    index = (index + 1) % SIZE;
                }
            }
        }

        // Not in the map
        None
    }

    /// Returns the value of the corresponding key
    fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        // Q is borrowed so we don't need it to be sized. This gives us better ergonomics with
        // types like `str` and `String`.
        Q: Hash + Eq + ?Sized,
        K: Borrow<Q>,
    {
        let build_hasher = H::default();
        let hash = build_hasher.hash_one(key);
        let mut index = (hash as usize) % SIZE;

        for _ in 0..SIZE {
            match self.meta.status[index] {
                Status::Free => {
                    // The entry is not in the hash map
                    return None;
                }
                Status::Used if unsafe { self.key_matches(index, key) } => {
                    return Some(unsafe { self.values[index].assume_init_ref() });
                }
                Status::Deleted | Status::Used => {
                    // FIXME: The table is full and the key is not present
                    index = (index + 1) % SIZE;
                }
            }
        }

        // Did not find it.
        None
    }

    /// Returns the most recent key-value pair that was either inserted or
    /// updated and is still present,
    fn get_last(&self) -> Option<(&K, &V)> {
        let index = self.meta.head;
        self.get_at_index(index)
    }

    /// returns the least recent key-value pair that was either inserted or
    /// updated and is still present
    fn get_first(&self) -> Option<(&K, &V)> {
        let index = self.meta.tail;
        self.get_at_index(index)
    }

    fn get_at_index(&self, index: usize) -> Option<(&K, &V)> {
        if INVALID_INDEX != index {
            debug_assert_eq!(self.meta.status[index], Status::Used);

            unsafe {
                Some((
                    self.keys[index].assume_init_ref(),
                    self.values[index].assume_init_ref(),
                ))
            }
        } else {
            None
        }
    }

    unsafe fn key_matches<Q>(&self, index: usize, key: &Q) -> bool
    where
        Q: Eq + ?Sized,
        K: Borrow<Q>,
    {
        let contained = self.keys[index].assume_init_ref().borrow();
        contained == key
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Status {
    Free,
    Used,
    Deleted,
}

// We really don't need all 64-bits of an index, considering no table will ever have that amount of
// RAM memory (at least within our lifetime?).
// Which means we could easily encode the option as part of the indices using MAX_USIZE.
type Index = usize;
const INVALID_INDEX: usize = usize::MAX;

/// Stores internal metadata for the table usage:
///  - A slot status indicating if the slot is valid, invalid or deleted.
///  - Linkage information to determine the order of entries, needed by `get_last` and `get_first`.
struct Meta<const SIZE: usize> {
    status: [Status; SIZE],
    // These 2 members form a doubly-linked list with the order of the elements.
    forward_links: [Index; SIZE],
    backward_links: [Index; SIZE],
    // Points to the most-recently used entry in the table, if any
    head: Index,
    // Points to the most-recently used entry in the table, if any
    tail: Index,
}

impl<const SIZE: usize> Meta<SIZE> {
    const fn new() -> Self {
        Self {
            status: [Status::Free; SIZE],
            forward_links: [INVALID_INDEX; SIZE],
            backward_links: [INVALID_INDEX; SIZE],
            head: INVALID_INDEX,
            tail: INVALID_INDEX,
        }
    }

    fn mark_used(&mut self, new_head: usize) {
        // We should never get an invalid index here
        debug_assert_ne!(INVALID_INDEX, new_head);

        if self.status[new_head] == Status::Used {
            // We need to remove the element first from the list, because the slot was already used
            self.mark_removed(new_head);
        }

        self.status[new_head] = Status::Used;

        if INVALID_INDEX != self.head {
            // There is at least one entry in the hash table
            // We need to update the head to point to the new index
            let prev_head = self.head;
            self.head = new_head;

            // The head should never have an element after it.
            debug_assert_eq!(self.forward_links[prev_head], INVALID_INDEX);

            self.forward_links[prev_head] = new_head;
            self.backward_links[new_head] = prev_head;
        } else {
            // We are inserting the first element into the table. There are no links back and
            // forth, just setting the head and tail will be enough.
            self.head = new_head;
            self.tail = new_head;
        }
    }

    fn mark_removed(&mut self, to_remove: usize) {
        // We should never get an invalid index here
        debug_assert_ne!(INVALID_INDEX, to_remove);
        debug_assert_eq!(self.status[to_remove], Status::Used);
        self.status[to_remove] = Status::Deleted;

        let prev_idx = self.backward_links[to_remove];
        let next_idx = self.forward_links[to_remove];

        self.forward_links[to_remove] = INVALID_INDEX;
        self.backward_links[to_remove] = INVALID_INDEX;

        if INVALID_INDEX != prev_idx {
            self.forward_links[prev_idx] = next_idx;
        } else {
            // The element was the tail, it has nothing before it.
            self.tail = next_idx;
        }

        if INVALID_INDEX != next_idx {
            self.backward_links[next_idx] = prev_idx;
        } else {
            // The element was the head, it has nothing after it.
            self.head = prev_idx;
        }
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn test_insert_and_retrieve() {
        let mut map = HashMap::new();
        map.insert("Name".to_string(), "Javier".to_string())
            .unwrap();
        assert!(matches!(map.get("Name"), Some(v) if v == "Javier"));
    }

    #[test]
    fn test_get_unknown_key() {
        let mut map = HashMap::new();
        map.insert("Name".to_string(), "Javier".to_string())
            .unwrap();
        assert!(matches!(map.get("Age"), None));
    }

    #[test]
    fn test_remove_key() {
        let mut map = HashMap::new();
        map.insert("Name".to_string(), "Javier".to_string())
            .unwrap();
        map.insert("Age".to_string(), "32".to_string()).unwrap();
        assert!(matches!(map.get("Age"), Some(age) if age == "32"));
        assert!(matches!(map.get("Name"), Some(v) if v == "Javier"));

        assert!(matches!(map.remove("Age"), Some((k, v)) if v == "32" && k == "Age"));

        assert!(matches!(map.get("Age"), None));
        assert!(matches!(map.get("Name"), Some(v) if v == "Javier"));
    }

    #[test]
    fn test_remove_unknown_key() {
        let mut map = HashMap::new();

        map.insert("Name".to_string(), "Javier".to_string())
            .unwrap();

        assert!(matches!(map.remove("Name"), Some((k,v)) if k == "Name" && v == "Javier"));
        assert!(matches!(map.remove("Name"), None));
    }

    #[test]
    fn test_insert_twice() {
        let mut map = HashMap::new();

        map.insert("key".to_string(), 234).unwrap();

        assert!(matches!(map.get("key"), Some(v) if *v == 234));

        map.insert("key".to_string(), 435).unwrap();

        assert!(matches!(map.get("key"), Some(v) if *v == 435));
    }

    #[test]
    fn test_hash_collision_and_deleted_entries() {
        let key_a = "A";
        let key_b = "B";

        // Use a tiny map, to make it easy to find collisions
        const SIZE: usize = 4;

        let hasher_builder = BuildHasherDefault::<DefaultHasher>::default();
        let hash_a = (hasher_builder.hash_one(key_a) as usize) % SIZE;
        let hash_b = (hasher_builder.hash_one(key_b) as usize) % SIZE;

        // Make sure we actually have colliding keys
        assert_eq!(hash_a, hash_b);

        let mut map = HashMap::with_capacity::<SIZE>();

        // Now push them into the map
        map.insert(key_a.to_string(), "value_a".to_string())
            .unwrap();
        map.insert(key_b.to_string(), "value_b".to_string())
            .unwrap();

        assert!(matches!(map.get(key_a), Some(value) if value == "value_a"));
        assert!(matches!(map.get(key_b), Some(value) if value == "value_b"));

        assert!(matches!(map.remove(key_a), Some((k, v)) if v == "value_a" && k == key_a));

        assert!(matches!(map.get(key_a), None));
        assert!(matches!(map.get(key_b), Some(v) if v == "value_b"));

        assert!(matches!(map.remove(key_b), Some((k, v)) if v == "value_b" && k == key_b));

        assert!(matches!(map.get(key_a), None));
        assert!(matches!(map.get(key_b), None));

        // Insert them back in opposite order, and repeat the checks
        map.insert(key_b.to_string(), "value_b".to_string())
            .unwrap();
        map.insert(key_a.to_string(), "value_a".to_string())
            .unwrap();

        assert!(matches!(map.get(key_a), Some(value) if value == "value_a"));
        assert!(matches!(map.get(key_b), Some(value) if value == "value_b"));

        assert!(matches!(map.remove(key_a), Some((k, v)) if v == "value_a" && k == key_a));

        assert!(matches!(map.get(key_a), None));
        assert!(matches!(map.get(key_b), Some(v) if v == "value_b"));

        assert!(matches!(map.remove(key_b), Some((k, v)) if v == "value_b" && k == key_b));

        assert!(matches!(map.get(key_a), None));
        assert!(matches!(map.get(key_b), None));
    }

    #[test]
    fn test_full_map() {
        let pairs = [(213, 455), (32, 54), (5463, 32), (56574, 2345)];

        const SIZE: usize = 4;
        let mut map = HashMap::with_capacity::<SIZE>();

        for (k, v) in pairs {
            map.insert(k, v).unwrap();
        }

        assert!(matches!(map.insert(0, 0), Err(Error::MapFull)));

        // Should be able to find all elements
        for (k, v) in pairs {
            assert!(matches!(map.get(&k), Some(inner) if *inner == v));
        }

        // Remove element that is not in the map returns an empty optional because it was not found
        assert!(map.remove(&0).is_none());

        // Remove them
        for (k, v) in pairs {
            assert!(
                matches!(map.remove(&k), Some((inner_k, inner_v)) if inner_k == k && inner_v == v)
            );
        }

        // They should be gone
        for (k, _) in pairs {
            assert!(matches!(map.get(&k), None));
        }

        // Inserting them again should work. Lets try in opposite order
        for (k, v) in pairs.into_iter().rev() {
            map.insert(k, v).unwrap();
        }

        assert!(matches!(map.insert(0, 0), Err(Error::MapFull)));

        // Should be able to find all elements
        for (k, v) in pairs {
            assert!(matches!(map.get(&k), Some(inner) if *inner == v));
        }
    }

    #[test]
    fn test_get_by_order() {
        let pairs = [(213, 455), (32, 54), (5463, 32), (56574, 2345)];
        let (first_key, first_val) = pairs.first().cloned().unwrap();
        let (last_key, last_val) = pairs.last().cloned().unwrap();

        let mut map = HashMap::new();

        assert!(map.get_last().is_none());
        assert!(map.get_first().is_none());

        for (k, v) in pairs {
            map.insert(k, v).unwrap();

            assert!(
                matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == first_key && *inner_v == first_val)
            );
            assert!(
                matches!(map.get_last(), Some((inner_k,inner_v)) if *inner_k == k && *inner_v == v)
            );
        }

        // Delete 3rd item, which should not change the values returned by first and last
        assert!(map.remove(&5463).is_some());
        assert!(
            matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == first_key && *inner_v == first_val)
        );
        assert!(
            matches!(map.get_last(), Some((inner_k,inner_v)) if *inner_k == last_key && *inner_v == last_val)
        );

        // Delete the last element which should now result in get_last returning the second entry
        assert!(map.remove(&last_key).is_some());
        assert!(
            matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == first_key && *inner_v == first_val)
        );
        assert!(
            matches!(map.get_last(), Some((inner_k, inner_v)) if *inner_k == pairs[1].0 && *inner_v == pairs[1].1)
        );

        // Delete the first entry, now we should see head and tail point to the same element
        assert!(map.remove(&first_key).is_some());
        assert!(
            matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == pairs[1].0 && *inner_v == pairs[1].1)
        );
        assert!(
            matches!(map.get_last(), Some((inner_k, inner_v)) if *inner_k == pairs[1].0 && *inner_v == pairs[1].1)
        );

        // Insert a new element
        assert!(map.insert(0, 0).is_ok());
        assert!(
            matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == pairs[1].0 && *inner_v == pairs[1].1)
        );
        assert!(
            matches!(map.get_last(), Some((inner_k, inner_v)) if *inner_k == 0 && *inner_v == 0)
        );

        // Update the previous element with a new value
        assert!(map.insert(32, 0x1234).is_ok());
        assert!(
            matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == 0 && *inner_v == 0)
        );
        assert!(
            matches!(map.get_last(), Some((inner_k, inner_v)) if *inner_k == 32 && *inner_v == 0x1234)
        );

        assert!(map.remove(&0).is_some());
        assert!(
            matches!(map.get_first(), Some((inner_k,inner_v)) if *inner_k == 32 && *inner_v == 0x1234)
        );
        assert!(
            matches!(map.get_last(), Some((inner_k, inner_v)) if *inner_k == 32 && *inner_v == 0x1234)
        );

        assert!(map.remove(&32).is_some());
        assert!(matches!(map.get_first(), None));
        assert!(matches!(map.get_last(), None));
    }
}