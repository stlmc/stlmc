package data

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



// VGraph is data structure for sending graph data usign JSON format.
// This graph may contain multiple CompositeGraph
// as well as multiple Propositions and Mode.
type VGraph struct {
	Graph []CompositeGraph
	Props []Proposition
	Mode []Mode
}

// Json2FullGraph generates FullGraph and its elements.
func Json2FullGraph(filename string) *FullGraph{
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

	fg := result.ToFullGraph()
	Db.Add(Counter, &fg)
	Counter++

	return &fg
}

// SendFullGraph2Json generates data that fits d3.js.
func SendFullGraph2Json(){
	fg := Db.Get(0)
	s := fg.Similar()
	fmt.Println("Composite Graph")
	fmt.Println(len(s))
	fmt.Println(s[0].Sub)
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