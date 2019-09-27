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
		FullGraph: [
			// FullGraph
			{
				"Name" : "x",
				"SubGraph": [
					{ "Data": [[x_0, y_0], ...,[x_n, y_n]] },
					{ "Data": [[x_0, y_0], ...,[x_n, y_n]] },
					{ "Data": [[x_0, y_0], ...,[x_n, y_n]] },
					{ "Data": [[x_0, y_0], ...,[x_n, y_n]] },
					...
				],
			},
		],
		"Proposition": [
			{
				"Name": "disl10",
				"Actual": "x2-x1 < 10",
				"Data": ["True", ...,"False"]
			},
			{
				"Name": "disl10",
				"Actual": "x2-x1 < 10",
				"Data": ["True", ...,"False"]
			},
			{
				"Name": "disl10",
				"Actual": "x2-x1 < 10",
				"Data": ["True", ...,"False"]
			},
			...
		],
	}


*/
package data
/*
type Point struct {
	X int	`json:"x"`
	Y int	`json:"y"`
}

type SubGraph struct {
	// Data is representing actual points.
	Data []Point					`json:"Data"`

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

type Proposition struct {
	Name string
	Actual string
	Data []string
}

type Mode struct {
	Name string
	Actual string
	Data []string
}

// FullGraph represents full size graph which has
// multiple subgraphs in it. The full size graph
// does not change after created. So, we don't need
// getter since FullGraph is struct which is public
// or setter for each member variables.
type FullGraph struct {

	// Name is a FullGraph variable name
	Name string

	// Size is a number of subgraphs
	Size int

	// SubGraph is actual data
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

}

func (sg *SubGraph) getSubPoint() {

	if len(sg.Data) == 0 {
		return
	}

	sg.maxWithX = &sg.Data[0]
	sg.minWithX = &sg.Data[0]
	sg.maxWithY = &sg.Data[0]
	sg.minWithY = &sg.Data[0]

	for _, e := range sg.Data {

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

func (sg *SubGraph) New(){
	sg.maxWithX = nil
	sg.minWithX = nil
	sg.maxWithY = nil
	sg.minWithY = nil
	sg.getSubPoint()
}

func (fg *FullGraph) New(){

	// generate subgraph

	fg.MaxWithX = nil
	fg.MinWithX = nil
	fg.MaxWithY = nil
	fg.MinWithY = nil
	fg.getSubPoint()
}


// getMax is calculate maximum point of full graph.
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
*/

var test = "ss"