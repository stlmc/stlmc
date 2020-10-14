package data


// IsInList check if elem is in list or not.
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