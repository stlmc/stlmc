package data

var Db Storage
var Counter = 0


func IsInList(list []int, elem int) bool{
	// check if i is in exclude list
	for _, e1 := range list {
		// if no do compare, else do nothing.
		if elem  == e1 {
			return true
		}
	}
	return false
}

func IsInListOfList(list [][]int, elem int) bool {

	for _, e := range list {
		if IsInList(e, elem) {
			return true
		}
	}
	return false
}