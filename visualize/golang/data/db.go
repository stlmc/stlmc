package data

// HashSet is a simple implementation of hashset
// in golang. Since golang itself uses hash table
// with data structure map, we can simply use this
// to make set.
//
// see: https://www.callicoder.com/golang-maps/

// Db is package-wide variable
// used for storing read JSON data
var Db storage

// Counter is used for indexing
// .workspace's file.
var Counter = 0

type storage struct {
	container map[int]*FullGraph
}


func (st *storage) Add(key int, value *FullGraph) {
	if st.container == nil {
		st.container = make(map[int]*FullGraph)
	}
	// Add new element if not exist.
	// Overwrite element if exist.
	st.container[key] = value
}

// Delete function doesn’t return any value.
// Also, it doesn’t do anything if the key
// doesn’t exist in the map.
func (st *storage) Delete(key int){
	delete(st.container, key)
}

func (st *storage) Get(key int) *FullGraph{
	value, ok := st.container[key]
	if ok {
		return value
	}
	return nil
}