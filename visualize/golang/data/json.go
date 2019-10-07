package data

import (
	"encoding/json"
	"io/ioutil"
	"log"
)



// Json2FullGraph generates FullGraph and its elements.
func Json2FullGraph(index int, filename string) *FullGraph{
	b, readErr := ioutil.ReadFile(filename)

	if readErr != nil {
		log.Println(readErr)
		return nil
	}
	var result FullGraph4Json
	unmarshalErr := json.Unmarshal(b, &result)

	if unmarshalErr != nil {
		log.Println(unmarshalErr)
		return nil
	}

	if result.IsEmpty() {
		return nil
	}


	fg := result.ToFullGraph()
	Db.Add(index, &fg)

	return &fg
}