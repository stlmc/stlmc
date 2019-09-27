package data

import (
	"encoding/json"
	"io/ioutil"
	"log"
)

/*
func Read(filename string) {
	b, err := ioutil.ReadFile(filename)

	if err != nil {
		log.Fatal(err)
	}

	json.Unmarshal(b, &)

}*/

func Write (filename string) {

	var points = []Point{Point{0, 0}, Point{1, 1}, Point{2, 2}, Point{3, 3}, Point{4, 4}, Point{5, 5}}

	var sg = SubGraph{Data: points}
	file, marshalErr := json.Marshal(sg)

	if marshalErr != nil {
		log.Fatal(marshalErr)
	}

	writeError := ioutil.WriteFile(filename, file, 0644)

	if writeError != nil {
		log.Fatal(writeError)
	}
}