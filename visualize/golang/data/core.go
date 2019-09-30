/*
Package data implements a simple library for stlMC visualization data.
The data will be drawing using 2d space. It means that visualization
itself is consist of (x, y) pair.

The aforementioned conceptual objects' implementation in golang is marked
with "Actual" and conceptual representation is marked with "Concept".
The visualization needs data structure for basic elements such as point object.
Point is a basic element (object) for representing graph base objects.

For stlMC, data point will be just tuple (x, y), since we will only support for 2d
graphs. And the points will be transformed into multiple arrays of points for visualization.

	point:
		Concept:
			(x, y)
		Actual:
			type Point struct {
				x int
				y int
			}

The actual implementation of graph that actually used for plotting 2d lines in the 
visualization is multiple arrays of points. This is because the visualizing engine we used is 
d3.js which requires one point stream for one line plot. For example, we need 2 sub-graphs (lines) 
for plotting V shape graph. One sub-graph for left side of V shape and the other for right side. 
In stlMC visualization tool, we need sub-graph (line) per interval for each variable.
So if you want to draw just a single graph that has 4 intervals, then you need (4 * sub-graphs * variable size)
for plotting it. For this reason we need sub-graph object for not just holding points but also be able to
recognized which it belongs to. Sub-graph object is using its index as uid (unique id).

	sub-graph:
		Concept:
			[(x_0, y_0), (x_1, y_1), ..., (x_n, y_n)]
		Actual:
			type SubGraph struct {
				Data []Point
				MaxWithX Point
				MinWithX Point
				MaxWithY Point
				MinWithY Point
			}


Now, we need a graph object for plotting the full size graph. The full size graph consists of multiple 
sub-graph. Full graph object needs many methods, since it will take care of whole data processing 
logic and else. The object will have: 
	1) name of graph 
	2) size of sub-graphs
	3) sub-graphs
and also have ability to: 
	1) get sub-graph's index and return related sub-graph
	2) get a maximum and minimum point in each sub-graph with respect to x value
	3) get a maximum and minimum point in each sub-graph with respect to y value
	4) get a maximum and minimum point in full-graph with respect to both x, y value (using 2, 3)

The full graph will be some kind of class but as we know that golang doesn't support class, 
we implemented with ordinary struct with functions. Full graph object has only 2 point variables, 
so it need to calculate maxPoint or minPoint before referencing them. The difference between SubGraph 
and [] Point is that, SubGraph is holding data that is related to actual sub-graph while [] Point 
is holding data that is related to not sub-graph but many points. Since Sub of FullGraph's index is
uid of each sub-graph, you can use same index at corresponding maxPoint and minPoint if you calculate any.
The calculating max and min point needs to assert denying access to uncalculated but existing sub-graph's
max and min point using maxPoint and minPoint. FullGraph's name and its sub-graphs name is same.

	full-graph:
		Concept:
			[[(x_0, y_0), (x_1, y_1), ..., (x_n, y_n)], ... ]
		Actual:
			type FullGraph struct {
				Name string
				Size int
				Sub []SubGraph
				MaxWithX *Point
				MinWithX *Point
				MaxWithY *Point
				MinWithY *Point
			}

This package also have methods for read and write mentioned objects into JSON format. This JSON file(s) will
be used in front-end (nodejs).

JSON format, for example:
	{
		"Variable": ["x", "y", "z"],

		"Interval": [
			{
				"Name" : "x",
				"intIndex": "0",
				"Points": [
					{"x": x_0, "y": y_0},
					...,
					{"x": x_n, "y": y_n}
				],
			},
		],

		"Proposition": [
			{
				"Name": "disl10"
				"Actual": "x2-x1 < 10"
				"Data": ["True", "False"]
			},
			{
				"Name": "s0"
				"Actual": "x2 > 10"
				"Data": ["True", "False"]
			},
		],

		"Mode": {
			"Name": ["(false, true)", "(true, true)", "(true, false)", "(false, false)"]
			"Data": [0, 1, 2, 3]
		},

	}
*/
package data

import (
	"fmt"
	"math"
)

// IJsonPoint is same as util.JsonPoint
// this one is needed, since golang does't
// allow "Import cycle" issue.
type IJsonPoint = [2]int

type Point struct {
	X float64	`json:"x"`
	Y float64	`json:"y"`
}

// SubGraphData is needed for json parsing.
// If you design SubGraph directly has SubGraphData,
// you might have <nil> for maxWithX, ..., maxWithY.
// In order to avoid such situation you need to
// use SubGraphData for parsing actual json data and
// wrapping data structure SubGraph for calculation.
//
// For example,
//	{
//		"name": "x",
//		"intIndex": 0,
//		"points: [
//			{"x": 0.0, "y": 2.1},
//			{"x": 1.1, "y": 10.0},
//			...
//			{"x": 10.1, "y": 12.1}
//		]
//	}
// The example represents variable x with its points
// at some interval. There might be many variables at
// the same interval. That is why we need another
// wrapping data structure.
// See: SubGraph.
type SubGraph4Json struct {
	Name string		`json:"name"`
	Index int		`json:"intIndex"`
	// Data is representing actual points.
	Data []Point	`json:"points"`
}

func (sg4j *SubGraph4Json) ToSubGraph() SubGraph{
	var sg SubGraph
	sg.Elem = sg4j
	sg.Init()
	return sg
}

// SubGraph represents one fragment that is divided by
// intervals. SubGraph is wrapping SubGraph4Json. So this
// one is used for calculating complicated jobs such as
// getting maximum or minimum point within interval.
// See: SubGraph4Json.
type SubGraph struct {
	// Elem is getting from json file
	Elem *SubGraph4Json
	// MaxWithX is maximum point with
	// respect to x axis
	maxWithX *Point

	// MinWithX is minimum point with
	// respect to x axis
	minWithX *Point

	// MaxWithY is maximum point with
	// respect to y axis
	maxWithY *Point

	// MinWithY is minimum point with
	// respect to y axis
	minWithY *Point
}

// getSubPoint is calculating minimum and maximum value
// that we cared and called when initializing SubGraph.
// This function is called only internally.
func (sg *SubGraph) getSubPoint() {

	if len(sg.Elem.Data) == 0 {
		return
	}

	sg.maxWithX = &sg.Elem.Data[0]
	sg.minWithX = &sg.Elem.Data[0]
	sg.maxWithY = &sg.Elem.Data[0]
	sg.minWithY = &sg.Elem.Data[0]

	for _, e := range sg.Elem.Data {

		// calculate maximum point and minimum in list
		// with respect to x
		if e.X > sg.maxWithX.X {
			sg.maxWithX = &e
		}

		if e.X < sg.minWithX.X {
			sg.minWithX = &e
		}


		// calculate maximum point and minimum in list
		// with respect to x
		if e.Y > sg.maxWithY.Y {
			sg.maxWithY = &e
		}

		if e.Y < sg.minWithY.Y {
			sg.minWithY = &e
		}
	}
}

func (sg *SubGraph) Init(){
	sg.maxWithX = nil
	sg.minWithX = nil
	sg.maxWithY = nil
	sg.minWithY = nil
	sg.getSubPoint()
}

// Proposition is representing proposition for
// visualize tool.
//
// For example,
//	{
//		"name": "reachability",
//		"actual: "x1 < 27",
//		"data": ["True", "False", "True", "False"]
//	}
type Proposition struct {
	Name string		`json:"name"`
	Actual string	`json:"actual"`
	Data []string	`json:"data"`
}

// TODO: Fill this part
type Mode struct {
	Name []string	`json:"name"`
	Data []int		`json:"data"`
}

// FullGraphData is used for parsing a json file.
// This data structure exist only 1 for 1 json file.
//
// For example,
//	{
//		"interval": [see_above_case]
//		"prop":	[see_above_case]
//		"mode": [see_above_case]
//	}
type FullGraph4Json struct {
	Var	[]string				`json:"variable"`
	Interval []SubGraph4Json 	`json:"interval"`
	Prop []Proposition 			`json:"prop"`
	Mode Mode					`json:"mode"`
}

// ToFullGraph returns FullGraph from FullGraph4Json
func (fg4j *FullGraph4Json) ToFullGraph() FullGraph{
	var fg FullGraph
	for i, _ := range fg4j.Interval {
		fg.Sub = append(fg.Sub, fg4j.Interval[i].ToSubGraph())
	}
	fg.Size = len(fg.Sub)
	fg.Prop = fg4j.Prop
	fg.Mode = fg4j.Mode
	fg.Var = fg4j.Var
	fg.Init()
	return fg
}

// FullGraph represents full size graph which has
// multiple subgraphs in it. The full size graph
// does not change after created. So, we don't need
// getter since FullGraph is struct which is public
// or setter for each member variables.
type FullGraph struct {

	// Var is holding a list of variables.
	Var []string

	// Size is a number of subgraphs,
	// this size is same as number of
	// intervals.
	Size int

	// Sub is actual data
	Sub []SubGraph

	// Prop is holding proposition
	Prop []Proposition

	// Mode get Mode type data
	Mode Mode

	// MaxWithX is FullGraph's maximum
	// point with respect to X axis
	MaxWithX *Point

	// MinWithX is FullGraph's minimum
	// point with respect to X axis
	MinWithX *Point

	// MaxWithY is FullGraph's maximum
	// point with respect to Y axis
	MaxWithY *Point

	// MinWithY is FullGraph's minimum
	// point with respect to Y axis
	MinWithY *Point
}

// getSubPoint is calculate maximum point of full graph.
// if ax is X it returns maximum point with respect to
// x axis otherwise will return y point. This function
// will called once (when the object is created).
func (fg *FullGraph) getSubPoint(){
	if len(fg.Sub) == 0 {
		return
	}

	fg.MaxWithX = fg.Sub[0].maxWithX
	fg.MinWithX = fg.Sub[0].minWithX
	fg.MaxWithY = fg.Sub[0].maxWithY
	fg.MinWithY = fg.Sub[0].minWithY


	for _, e := range fg.Sub{

		// calculate maximum point and minimum in point list
		// with respect to x
		if e.maxWithX.X > fg.MaxWithX.X {
			fg.MaxWithX = e.maxWithX
		}

		if e.minWithX.X < fg.MinWithX.X {
			fg.MinWithX = e.minWithX
		}

		// calculate maximum point and minimum in point list
		// with respect to y
		if e.maxWithY.Y > fg.MaxWithY.Y {
			fg.MaxWithY = e.maxWithY
		}

		if e.minWithY.Y < fg.MinWithY.Y {
			fg.MinWithY = e.minWithY
		}
	}
}

func (fg *FullGraph) Init(){
	fg.MaxWithX = nil
	fg.MinWithX = nil
	fg.MaxWithY = nil
	fg.MinWithY = nil
	fg.getSubPoint()
}

// Similar returns similar graphs with respect to y ranges.
// This is used for determine similar scale graph.
func (fg *FullGraph) SameGraph() []CompositeGraph {

	// Gathering same graph first
	var same []CompositeGraph

	// iterate with variable names
	for _, e := range fg.Var {
		var tmp CompositeGraph
		// iterate through whole list of subgraphs
		for _, el := range fg.Sub {
			// if find one that matches name
			if el.Elem.Name == e {
				tmp.Add(el)
			}
		}
		tmp.Init()
		same = append(same, tmp)
	}
	return same
}

// Similar returns similar graphs with respect to y ranges.
// This is used for determine similar scale graph.
func (fg *FullGraph) Similar() []CompositeGraph {

	// Gathering same graph first
	var same []CompositeGraph
	var fs []float64

	// iterate with variable names
	// such as ["x", "y", "z"]. e is one of "x" or
	// "y" or "z".
	for _, e := range fg.Var {
		var tmp CompositeGraph
		// iterate through whole list of subgraphs.
		for _, el := range fg.Sub {
			// if find one that matches name
			if el.Elem.Name == e {
				tmp.Add(el)
			}
		}
		tmp.Init()
		fmt.Println("inside")
		fmt.Println(tmp.Sub[0].Elem)
		fs = append(fs, tmp.FootStep)
		same = append(same, tmp)
	}

	// exclude index list. i.e already found similar one
	// and gathered with similar ones.
	var exclude [][]int

	// find similar ones
	for i, _ := range fs {
		// if index is not in exclude list
		if !IsInListOfList(exclude, i) {
			var tmp []int
			for j := i + 1; j < len(fs); j++ {
				// if two deltas abs value is less than 10
				// we determined that it has similar scale
				if math.Abs(fs[i] - fs[j]) < 10 {
					tmp = append(tmp, j)
				}
			}
			exclude = append(exclude, tmp)
		}
	}

	var similar []CompositeGraph
	for _, e := range exclude {
		var empty CompositeGraph
		for _, el := range e {
			empty.Concat(same[el])
		}
		similar = append(similar, empty)
	}

	return similar

}

// CompositeGraph contains a list of SubGraph that have same logically
// meaning that we want for them to have. This data structure holds
// several fragments of lines that have the same meaning. CompositeGraph
// can be used to make a gathered graphs with same meaning.
//
// For example,
// 		1) Fragment of lines with same variable name. i.e. same graph.
// 		2) Fragment of lines with same variable name and similar scale.
// 			It means if you have 2 graphs with graph 1's range is between
// 			[100, 500] and graph 2's range is between [0.1, 1]. Then, you will
// 			have 2 CompositeGraph. However if both graphs have similar y ranges
// 			then, you will have only 1 CompositeGraph.
type CompositeGraph struct {
	Sub []SubGraph

	// MaxWithX is FullGraph's maximum
	// point with respect to X axis
	MaxWithX *Point

	// MinWithX is FullGraph's minimum
	// point with respect to X axis
	MinWithX *Point

	// MaxWithY is FullGraph's maximum
	// point with respect to Y axis
	MaxWithY *Point

	// MinWithY is FullGraph's minimum
	// point with respect to Y axis
	MinWithY *Point

	// PointCounter counts number of points
	PointCounter int
	DeltaY float64

	// FootStep is calculating scale factor.
	FootStep float64
}


func (cg *CompositeGraph) Concat(cg2 CompositeGraph) {
	for _, e := range cg2.Sub {
		cg.Sub = append(cg.Sub, e)
	}
	cg.Init()
}


func (cg *CompositeGraph) Add(sub SubGraph) {
	cg.Sub = append(cg.Sub, sub)
}

// getSubPoint is calculate maximum point of full graph.
// if ax is X it returns maximum point with respect to
// x axis otherwise will return y point. This function
// will called once (when the object is created).
func (cg *CompositeGraph) getSubPoint(){
	if len(cg.Sub) == 0 {
		return
	}

	cg.MaxWithX = cg.Sub[0].maxWithX
	cg.MinWithX = cg.Sub[0].minWithX
	cg.MaxWithY = cg.Sub[0].maxWithY
	cg.MinWithY = cg.Sub[0].minWithY


	for _, e := range cg.Sub{

		// calculate maximum point and minimum in point list
		// with respect to x
		if e.maxWithX.X > cg.MaxWithX.X {
			cg.MaxWithX = e.maxWithX
		}

		if e.minWithX.X < cg.MinWithX.X {
			cg.MinWithX = e.minWithX
		}

		// calculate maximum point and minimum in point list
		// with respect to y
		if e.maxWithY.Y > cg.MaxWithY.Y {
			cg.MaxWithY = e.maxWithY
		}

		if e.minWithY.Y < cg.MinWithY.Y {
			cg.MinWithY = e.minWithY
		}

		cg.PointCounter += len(e.Elem.Data)
	}

	cg.DeltaY = cg.MaxWithY.Y - cg.MinWithY.Y
	cg.FootStep = cg.DeltaY / float64(cg.PointCounter)

}

func (cg *CompositeGraph) Init(){
	cg.MaxWithX = nil
	cg.MinWithX = nil
	cg.MaxWithY = nil
	cg.MinWithY = nil
	cg.DeltaY = 0.0
	cg.PointCounter = 0
	cg.FootStep = 0.0
	cg.getSubPoint()
}

