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

		"Mode": [
			{
				"Name": ["(false, true)", "(true, true)", "(true, false)", "(false, false)"]
				"Data": [0, 1, 2, 3]
			},
		]

	}
*/
package data

import (
	"math"
)

type Point struct {
	X float64	`json:"x"`
	Y float64	`json:"y"`
}

type Range struct {

	MaxXfloat float64		`json:"max_x"`
	MinXfloat float64		`json:"min_x"`
	MaxYfloat float64		`json:"max_y"`
	MinYfloat float64		`json:"min_y"`

	// MaxWithX is maximum point with
	// respect to X axis
	MaxX *Point		`json:"max_with_x"`

	// MinWithX is point with respect
	// to X axis
	MinX *Point		`json:"min_with_x"`

	// MaxWithY is point with respect
	// to Y axis
	MaxY *Point		`json:"max_with_y"`

	// MinWithY is point with respect
	// to Y axis
	MinY *Point		`json:"min_with_y"`
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


// GraphAsName holds data with names, this is nothing to
// do with intervals. When you need name "x1"'s all data, then
// you should want this structure.
type GraphAsName struct {
	Name string		`json:"name"`
	Data []Point	`json:"points"`
}

// GraphAsName4Json holds The index and GraphAsName's list which
// represents similar graph. For example, if you get similar graph
// using Similar() in FullGraph that ["x1", "x2"] is similar than,
// GraphAsName4Json will looks something like,
// {
//		Index: 0,
//		GraphAsName: [
//			{
//				Name: "x1",
//				Data: [ ... ]
//			},
//			{
//				Name: "x2",
//				Data: [ ... ]
//			},
//		]
// }
type GraphAsName4Json struct {
	Index int			`json:"index"`
	Data []GraphAsName	`json:"graph"`
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
	Range Range
}

func (sg *SubGraph) ToSubGraph4Json() SubGraph4Json{
	return *sg.Elem
}

// getSubPoint is calculating minimum and maximum value
// that we cared and called when initializing SubGraph.
// This function is called only internally.
func (sg *SubGraph) getSubPoint() {

	if len(sg.Elem.Data) == 0 {
		return
	}

	sg.Range.MaxX = &sg.Elem.Data[0]
	sg.Range.MinX = &sg.Elem.Data[0]
	sg.Range.MaxY = &sg.Elem.Data[0]
	sg.Range.MinY = &sg.Elem.Data[0]

	for i, _ := range sg.Elem.Data {
		// calculate maximum point and minimum in list
		// with respect to x
		if sg.Elem.Data[i].X > sg.Range.MaxX.X {
			sg.Range.MaxX = &sg.Elem.Data[i]

		}

		if sg.Elem.Data[i].X < sg.Range.MinX.X {
			sg.Range.MinX = &sg.Elem.Data[i]
		}


		// calculate maximum point and minimum in list
		// with respect to y
		if sg.Elem.Data[i].Y > sg.Range.MaxY.Y {
			sg.Range.MaxY = &sg.Elem.Data[i]
		}

		if sg.Elem.Data[i].Y < sg.Range.MinY.Y {
			sg.Range.MinY = &sg.Elem.Data[i]
		}
	}

	sg.Range.MinXfloat = sg.Range.MinX.X
	sg.Range.MinYfloat = sg.Range.MinY.Y
	sg.Range.MaxXfloat = sg.Range.MaxX.X
	sg.Range.MaxYfloat = sg.Range.MaxY.Y

}

func (sg *SubGraph) Init(){
	sg.Range.MaxX = nil
	sg.Range.MinX = nil
	sg.Range.MaxY = nil
	sg.Range.MinY = nil
	sg.Range.MinXfloat = 0.0
	sg.Range.MaxXfloat = 0.0
	sg.Range.MinYfloat = 0.0
	sg.Range.MaxYfloat = 0.0
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
	Name string			`json:"name"`
	Actual string		`json:"actual"`
	Data []string		`json:"data"`
}

// TODO: error
type Mode struct {
	Name string		`json:"name"`
	Type string		`json:"type"`
	Data interface{}`json:"data"`
}

// IntervalInfo implements interval's range info
// which saves information such as each interval's
// start or end points.
type IntervalInfo struct {
	IntIndex int		`json:"intIndex"`
	Range [2]float64	`json:"range"`
	Data []float64		`json:"data"`
}

// FullGraphData is used for parsing a json file.
// This data structure exist only 1 for 1 json file.
//
// For example,
//	{
//		"variable": [see_above_case]
//		"interval": [see_above_case]
//		"prop":	[see_above_case]
//		"mode": [see_above_case]
//	}
type FullGraph4Json struct {
	Var	[]string				`json:"variable"`
	Interval []SubGraph4Json 	`json:"interval"`
	Prop []Proposition 			`json:"prop"`
	Mode []Mode					`json:"mode"`
	IntervalInfo []IntervalInfo	`json:"intervalInfo"`
}


func (fg4j *FullGraph4Json) IsEmpty() bool {
	if len(fg4j.Var) == 0 {
		return true
	}

	if len(fg4j.Interval) == 0 {
		return true
	}

	if len(fg4j.Prop) == 0 {
		return true
	}

	if len(fg4j.Mode) == 0 {
		return true
	}

	if len(fg4j.IntervalInfo) == 0 {
		return true
	}

	return false
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
	fg.IntervalInfo = fg4j.IntervalInfo
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
	Mode []Mode

	// IntervalInfo get interval information
	IntervalInfo []IntervalInfo

	Range Range
}

func (fg *FullGraph) GetXData() []float64 {
	var xList []float64

	for _, e := range fg.Sub {

		for _, e1 := range e.Elem.Data {
			xList = append(xList, e1.X)
		}
	}
	return xList
}


func (fg *FullGraph) ToFullGraph4Json() FullGraph4Json{
	var fg4j FullGraph4Json
	fg4j.Var = fg.Var
	fg4j.Prop = fg.Prop
	fg4j.Mode = fg.Mode
	fg4j.IntervalInfo = fg.IntervalInfo
	var sub []SubGraph4Json
	for i, _ := range fg.Sub {
		sub = append(sub, fg.Sub[i].ToSubGraph4Json())
	}
	fg4j.Interval = sub
	return fg4j
}

// getSubPoint is calculate maximum point of full graph.
// if ax is X it returns maximum point with respect to
// x axis otherwise will return y point. This function
// will called once (when the object is created).
func (fg *FullGraph) getSubPoint(){
	if len(fg.Sub) == 0 {
		return
	}

	fg.Range.MaxX = fg.Sub[0].Range.MaxX
	fg.Range.MinX = fg.Sub[0].Range.MinX
	fg.Range.MaxY = fg.Sub[0].Range.MaxY
	fg.Range.MinY = fg.Sub[0].Range.MinY


	for _, e := range fg.Sub{

		// calculate maximum point and minimum in point list
		// with respect to x
		if e.Range.MaxX.X > fg.Range.MaxX.X {
			fg.Range.MaxX = e.Range.MaxX
		}

		if e.Range.MinX.X < fg.Range.MinX.X {
			fg.Range.MinX = e.Range.MinX
		}

		// calculate maximum point and minimum in point list
		// with respect to y
		if e.Range.MaxY.Y > fg.Range.MaxY.Y {
			fg.Range.MaxY = e.Range.MaxY
		}

		if e.Range.MinY.Y < fg.Range.MinY.Y {
			fg.Range.MinY = e.Range.MinY
		}
	}

	fg.Range.MinXfloat = fg.Range.MinX.X
	fg.Range.MinYfloat = fg.Range.MinY.Y
	fg.Range.MaxXfloat = fg.Range.MaxX.X
	fg.Range.MaxYfloat = fg.Range.MinY.Y
}

func (fg *FullGraph) Init(){
	fg.Range.MaxX = nil
	fg.Range.MinX = nil
	fg.Range.MaxY = nil
	fg.Range.MinY = nil
	fg.Range.MinXfloat = 0.0
	fg.Range.MinYfloat = 0.0
	fg.Range.MaxXfloat = 0.0
	fg.Range.MaxYfloat = 0.0
	fg.getSubPoint()
}

// SameGraph returns similar graphs with respect to y ranges.
// This is used for determine similar scale graph.
func (fg *FullGraph) SameGraph() []CompositeGraph {

	// Gathering same graph together in the array.
	// find same graph according to its name
	// for example, if your "interval" has [{"name": "x" ... },
	// {"name": "y" ...} then, you can find 2 CompositeGraph.
	var same []CompositeGraph

	// iterate with variable names
	// such as ["x", "y", "z"]. e is one of "x" or
	// "y" or "z".
	for _, e := range fg.Var {
		var tmp CompositeGraph
		tmp.Name = e
		// iterate through whole list of subgraphs
		for _, el := range fg.Sub {
			// if find one that matches name
			if el.Elem.Name == e {
				tmp.Name = e
				tmp.Add(el)
			}
		}
		tmp.Init()

		same = append(same, tmp)
	}
	return same
}

// MakeSameGraphAsNameMap returns same graphs with respect to name
func (fg *FullGraph) MakeSameGraphAsNameMap() map[string]GraphAsName {

	// Gathering same graph together in the array.
	// find same graph according to its name
	// for example, if your "interval" has [{"name": "x" ... },
	// {"name": "y" ...} then, you can find 2 CompositeGraph.
	var same = make(map[string]GraphAsName, 0)

	// iterate with variable names
	// such as ["x", "y", "z"]. e is one of "x" or
	// "y" or "z".
	for _, e := range fg.Var {
		var tmp GraphAsName
		// iterate through whole list of subgraphs
		for _, el := range fg.Sub {
			// if find one that matches name
			if el.Elem.Name == e {
				tmp.Name = e
				tmp.Data = append(tmp.Data, el.Elem.Data...)
			}
		}
		same[e] = tmp
	}

	return same
}

// Similar returns similar graphs with respect to y ranges and
// its variable list. This is used for determine similar scale graph.
func (fg *FullGraph) Similar() []CompositeGraph {

	// Gathering same graph first
	same := fg.SameGraph()
	var sameMap = make(map[int]CompositeGraph)
	// transform list to Map, key as list index
	// value as its element: CompositeGraph
	for i, _ := range same {
		sameMap[i] = same[i]
	}

	// iterate through CompositeGraph array i.e. CompositeGraph1,
	// CompositeGraph2, ...
	for i, e := range sameMap {
	// iterate through whole list of subgraphs.
	// if not in the savedIndex.
		for j, e1 := range sameMap {
			// compare CompositeGraph pairwise way.
			// if two graphs maximum y value's difference is less than 1
			// and minimum y value's difference is less than 1 then, we
			// determine that it is same.
			if math.Abs(e.Range.MaxY.Y-e1.Range.MaxY.Y) < 10 && i != j {
				if math.Abs(e.Range.MinY.Y-e1.Range.MinY.Y) < 10 {
					// same case
					e.Concat(e1)
					delete(sameMap, i)
					delete(sameMap, j)
					sameMap[i] = e
				}
			}
		}
	}

	var res []CompositeGraph

	for _, v := range sameMap {
		res = append(res, v)
	}

	return res
}

func (fg *FullGraph) ToCompositeGraph4Json() CompositeGraph4Json{
	var cg = fg.Similar()

	var cg4j CompositeGraph4Json
	cg4j.Var = fg.Var
	cg4j.Mode = fg.Mode
	cg4j.Prop = fg.Prop
	cg4j.Xdata = fg.GetXData()
	cg4j.IntervalInfo = fg.IntervalInfo
	cg4j.FullRange = make([]float64, 0)
	graphAsNameMap := fg.MakeSameGraphAsNameMap()
	// iterate through each variable's fullgraph
	for i, _ := range cg {
		// this one contains all subgraphs of fullgraph
		var sub []SubGraph4Json
		var csg4j CompositeSubGraph4Json
		var similarVariable []string
		for _, elem := range cg[i].Sub {
			sub = append(sub, elem.ToSubGraph4Json())
			similarVariable = append(similarVariable, elem.Elem.Name)
		}
		csg4j.Graph = sub
		csg4j.Index = i

		csg4j.Range.MaxY = cg[i].Range.MaxY
		csg4j.Range.MinY = cg[i].Range.MinY
		csg4j.Range.MaxX = cg[i].Range.MaxX
		csg4j.Range.MinX = cg[i].Range.MinX

		csg4j.Range.MinXfloat = cg[i].Range.MinXfloat
		csg4j.Range.MaxXfloat = cg[i].Range.MaxXfloat
		csg4j.Range.MinYfloat = cg[i].Range.MinYfloat
		csg4j.Range.MaxYfloat = cg[i].Range.MaxYfloat

		cg4j.Interval = append(cg4j.Interval, csg4j)

		// GraphAsName4Json
		var gs4j GraphAsName4Json
		gs4j.Index = i
		for _, sv := range similarVariable {
			gs4j.Data = append(gs4j.Data, graphAsNameMap[sv])
		}
		cg4j.DataByName = append(cg4j.DataByName, gs4j)
	}
	for _, e := range fg.IntervalInfo {
		if !isInList(cg4j.FullRange, e.Range[0]) {
			cg4j.FullRange = append(cg4j.FullRange, e.Range[0])
		}

		if !isInList(cg4j.FullRange, e.Range[1]) {
			cg4j.FullRange = append(cg4j.FullRange, e.Range[1])
		}
	}

	return cg4j
}

func isInList(l []float64, elem float64) bool{
	for _, e := range l {
		if e == elem {
			return true
		}
	}
	return false
}

type CompositeSubGraph4Json struct {
	Index int					`json:"index"`
	Graph []SubGraph4Json		`json:"graph"`
	Range Range					`json:"range"`
}

type CompositeGraph4Json struct {
	Var	[]string						`json:"variable"`
	Interval []CompositeSubGraph4Json 	`json:"interval"`
	DataByName []GraphAsName4Json		`json:"dataByName"`
	Prop []Proposition 					`json:"prop"`
	Mode []Mode							`json:"mode"`
	Xdata []float64						`json:"xdata"`
	IntervalInfo []IntervalInfo			`json:"intervalInfo"`
	FullRange []float64					`json:"fullIntervalRange"`
}

// CompositeGraph contains a list of SubGraph that have same logical
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

	Name string

	Range Range

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
	// recalculate
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

	cg.Range.MaxX = cg.Sub[0].Range.MaxX
	cg.Range.MinX = cg.Sub[0].Range.MinX
	cg.Range.MaxY = cg.Sub[0].Range.MaxY
	cg.Range.MinY = cg.Sub[0].Range.MinY


	for _, e := range cg.Sub{

		// calculate maximum point and minimum in point list
		// with respect to x
		if e.Range.MaxX.X > cg.Range.MaxX.X {
			cg.Range.MaxX = e.Range.MaxX
		}

		if e.Range.MinX.X < cg.Range.MinX.X {
			cg.Range.MinX = e.Range.MinX
		}

		// calculate maximum point and minimum in point list
		// with respect to y
		if e.Range.MaxY.Y > cg.Range.MaxY.Y {
			cg.Range.MaxY = e.Range.MaxY
		}

		if e.Range.MinY.Y < cg.Range.MinY.Y {
			cg.Range.MinY = e.Range.MinY
		}

		cg.PointCounter += len(e.Elem.Data)
	}

	cg.DeltaY = cg.Range.MaxY.Y - cg.Range.MinY.Y
	cg.FootStep = cg.DeltaY / float64(cg.PointCounter)
	cg.Range.MinXfloat = cg.Range.MinX.X
	cg.Range.MinYfloat = cg.Range.MinY.Y
	cg.Range.MaxXfloat = cg.Range.MaxX.X
	cg.Range.MaxYfloat = cg.Range.MaxY.Y

}

func (cg *CompositeGraph) Init(){
	cg.Range.MaxX = nil
	cg.Range.MinX = nil
	cg.Range.MaxY = nil
	cg.Range.MinY = nil
	cg.Range.MinXfloat = 0.0
	cg.Range.MinYfloat = 0.0
	cg.Range.MaxXfloat = 0.0
	cg.Range.MaxYfloat = 0.0

	cg.DeltaY = 0.0
	cg.PointCounter = 0
	cg.FootStep = 0.0
	cg.getSubPoint()
}

