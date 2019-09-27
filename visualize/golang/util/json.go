package util

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"log"
)

// JsonPoint is json representation of core's Point struct.
// For example, if you have Point {x, y} then it is same as
// [x, y] in Json format. This kind of transformation is
// necessary for front-end library, d3.js.
type JsonPoint = [2]float64

type JsonSubGraph struct {
	Name string 	`json:"name"`
	// Data is representing actual points.
	Points []JsonPoint	`json:"points"`
}

type Propl struct {
	N string `json:"reachability"`
}

type Propg struct {
	N []string `json:"reachability"`
}

type Gee struct {
	Subb []JsonSubGraph `json:"data"`
	Prr	Propl				`json:"proplist"`
	pr2 Propg `json:"prop"`
}

// Read generates UnitGraph and its elements.
func Read(filename string) {
	b, err := ioutil.ReadFile(filename)

	if err != nil {
		log.Fatal(err)
	}
	var result Gee
	uerr := json.Unmarshal(b, &result)

	if uerr != nil {
		log.Fatal(uerr)
	}

	fmt.Println(result)
	fmt.Println(result.Subb[0].Points[1][0])

}

func Write (filename string) {

	/*var points = []data.Point{{X: 0, Y:0}, data.Point{X: 1, Y: 1}, data.Point{X:2, Y:2}, data.Point{X:3, Y:3}, data.Point{X:4, Y:4}, data.Point{X:5, Y:5}}
	var jpoints []*JsonPoint*/
	/*for _, e := range points {
		jpoints = append(jpoints, e.JsonPoint())
	}*/
	/*var sg = JsonSubGraph{Data: jpoints}
	file, marshalErr := json.Marshal(sg)

	if marshalErr != nil {
		log.Fatal(marshalErr)
	}

	writeError := ioutil.WriteFile(filename, file, 0644)

	if writeError != nil {
		log.Fatal(writeError)
	}*/
}