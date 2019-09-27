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
In stlMC visualization tool, we need sub-graph (line) per interval. So if you want to draw just 
a single graph that has 4 intervals, then you need 4 sub-graphs for plotting it. 
For this reason we need sub-graph object for not just holding points but also be able to 
recognized which it belongs to. Sub-graph object is using its index as uid (unique id).

	sub-graph:
		Concept:
			[(x_0, y_0), (x_1, y_1), ..., (x_n, y_n)]
		Actual:
			type SubGraph = []Point

Now, we need a graph object for plotting the full size graph. The full size graph consists of multiple 
sub-graph. Full graph object needs many methods, since it will take care of whole data processing 
logic and else. The object will have: 
	1) name of graph 
	2) size of sub-graphs 
	3) name of sub-graphs 
	4) sub-graphs itself
and also have ability to: 
	1) get sub-graph's name and return related sub-graph
	2) get a maximum and minimum point in each sub-graph with respect to x value
	3) get a maximum and minimum point in each sub-graph with respect to y value
	4) get a maximum and minimum point in full-graph with respect to both x, y value (using 2, 3)

The full graph will be some kind of class but as we know that golang doesn't support class, 
we implemented with ordinary struct with functions. Full graph object has only 2 point variables, 
so it need to calculate maxPoint or minPoint before referencing them. The difference between SubGraph 
and [] Point is that, SubGraph is holding data that is related to actual sub-graph while [] Point 
is holding data that is related to not sub-graph but many points. Since subgraph of FullGraph's index is 
uid of each sub-graph, you can use same index at corresponding maxPoint and minPoint if you calculate any.
The calculating max and min point needs to assert denying access to uncalculated but existing sub-graph's
max and min point using maxPoint and minPoint.

	full-graph:
		Concept:
			[[(x_0, y_0), (x_1, y_1), ..., (x_n, y_n)], ... ]
		Actual:
			type FullGraph struct {
				subgraph SubGraph
				maxPoint []Point
				minPoint []Point
			}

This package also have methods for read and write mentioned objects into JSON format. This JSON file(s) will
be used in front-end (nodejs).
*/
package data

type Point struct {
	x int
	y int
}

type SubGraph = []Point

type FullGraph struct {
	Name string
	Size int
	SubName []string
	Subgraph SubGraph
	MaxPoint []Point
	MinPoint []Point
}

// GetMaxPoint is calculate maximum point of full graph.
func (fg *FullGraph) GetMaxPoint() (Point, bool){
	var max Point
	if len(fg.MaxPoint) == 0 {
		return Point{0, 0}, false
	}
	max = fg.MaxPoint[0]
	for _, e := range fg.MaxPoint{
		if e.x > max.x {
			max = e
		}
	}
	return max, true
}

// GetMinPoint is calculate minimum point of full graph.
// if it returns true then there exists min point in the
// full graph, otherwise false.
func (fg *FullGraph) GetMinPoint() (Point, bool){
	var min Point
	if len(fg.MinPoint) == 0 {
		return Point{0, 0}, false
	}
	min = fg.MinPoint[0]
	for _, e := range fg.MinPoint{
		if e.x < min.x {
			min = e
		}
	}
	return min, true
}
