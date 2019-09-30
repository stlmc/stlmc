package data

// HashSet is a simple implementation of hashset
// in golang. Since golang itself uses hash table
// with data structure map, we can simply use this
// to make set.
//
// see: https://www.callicoder.com/golang-maps/
type Storage struct {
	container map[int]*FullGraph
}

func (st *Storage) Add(key int, value *FullGraph) {
	if st.container == nil {
		st.container = make(map[int]*FullGraph)
	}
	st.container[key] = value
}

// Delete function doesn’t return any value.
// Also, it doesn’t do anything if the key
// doesn’t exist in the map.
func (st *Storage) Delete(key int){
	delete(st.container, key)
}

func (st *Storage) Get(key int) *FullGraph{
	value, ok := st.container[key]
	if ok {
		return value
	}
	return nil
}