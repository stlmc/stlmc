package data

import (
	"encoding/json"
	"golang/logger"
	"io/ioutil"
	"log"
)




// VGraph is data structure for sending graph data usign JSON format.
// This graph may contain multiple CompositeGraph
// as well as multiple Propositions and Mode.
type VGraph struct {
	Graph []CompositeGraph
	Props []Proposition
	Mode []Mode
}

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

	fg := result.ToFullGraph()
	Db.Add(index, &fg)

	return &fg
}

// SendFullGraph2Json generates data that fits d3.js.
func SendFullGraph2Json(){
	fg := Db.Get(0)
	s := fg.Similar()
	logger.Logger.Debug("Composite Graph : ")
	for _, e := range s[0].Sub {
		logger.Logger.Debug(e.Elem)
	}
}