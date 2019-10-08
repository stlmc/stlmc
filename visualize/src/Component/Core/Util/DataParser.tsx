/**
 * Basic wrapper class for *visualize* **project**.
 * This class uses MathModel's objects and this class is extremely specific
 * to certain project. Do not reuse this class. This is just wrapper class!
 *
 * Written by Geunyeol Ryu
 * @ 2019.06.22
 */

/**
 * Packages.
 */

export interface Proposition {
    name: string;
    actual: string;
    data: [number, number][][];
}

export interface IntervalInfo {
    intIndex: number;
    range: number[];
    data: number[];
}

export interface Mode {
    name: string;
    type: string;
    actual: string[];
    data: [number, number][][];
}

class Json {
    /**
     * Internally has intervals.
     */
    private _intervalsMap: Map<number, [number, number][][]> = new Map<number, [number, number][][]>();
    private _intervalVarMap: Map<number, string[]> = new Map<number, string[]>();

    private _xRangeMap: Map<number, [number, number]> = new Map<number, [number, number]>();
    private _yRangeMap: Map<number, [number, number]> = new Map<number, [number, number]>();
    private _graph_size: number = 0;

    private maxX: number = 0.0;
    private minX: number = 0.0;
    private totalMaxX: number = 0.0;
    private totalMinX: number = 0.0;
    private _isEmpty: Boolean = true;
    private _var_list: string[] = [];
    private _x_data_list: number[] = [];

    private _interval_flat_list: number[] = [];
    // Array of propositions. ["x>1", "x<0", ...]

    private _interval_info: Map<number, IntervalInfo> = new Map<number, IntervalInfo>();
    // i'th graph with auto interval and proposition
    private _propMap: Map<number, Proposition> = new Map<number, Proposition>();
    private _modeMap: Map<number, Mode> = new Map<number, Mode>();

    /**
     *
     * @param _jsonString String parsing by internal json parser to string.
     */
    constructor(
        private _jsonString: string = ""
    ) {
        //...
    }

    xRange(index: number): ([number, number] | undefined) {
        return this._xRangeMap.get(index);
    }

    yRange(index: number): ([number, number] | undefined) {
        return this._yRangeMap.get(index);
    }

    get variables() {
        return this._var_list;
    }

    get xlist() {
        return this._x_data_list;
    }

    GetGraph(index: number): ([number, number][][] | undefined) {
        return this._intervalsMap.get(index)
    }

    GetVar(index:number): (string[] | undefined) {
        return this._intervalVarMap.get(index);
    }

    GetGraphSize(): number {
        return this._graph_size;
    }

    GetIntervalSize(): number {
        return this._intervalsMap.size;
    }

    GetIntervalInfo(index: number) {
        return this._interval_info.get(index);
    }

    GetModeSize() {
        return this._modeMap.size;
    }

    GetMode(index: number) {
        return this._modeMap.get(index);
    }


    GetIntervalInfoFlat() {
        return this._interval_flat_list;
    }

    get varMap(){
        return this._intervalVarMap;
    }

    get map() {
        return this._intervalsMap;
    }

    get modeMap() {
        return this._modeMap;
    }

    // Get data list related to intervals from map structure.
    GetProp(index: number) {
        return this._propMap.get(index);
    }

    get propMap() {
        return this._propMap;
    }

    get propSize() {
        return this._propMap.size;
    }


    get MaxX() {
        return this.maxX;
    }

    get MinX() {
        return this.minX;
    }

    get TotalMaxX() {
        return this.totalMaxX;
    }

    get TotalMinX() {
        return this.totalMinX;
    }

    clearAll() {
        this._intervalsMap.clear();
        this._intervalVarMap.clear();
        this._xRangeMap.clear();
        this._yRangeMap.clear();
        this._graph_size = 0;

        this.maxX = 0.0;
        this.minX = 0.0;
        this.totalMaxX = 0.0;
        this.totalMinX = 0.0;
        this._isEmpty = true;
        this._var_list = [];
        this._x_data_list = [];

        this._interval_flat_list = [];
        // Array of propositions. ["x>1", "x<0", ...]

        this._interval_info.clear();
        // i'th graph with auto interval and proposition
        this._propMap.clear();
        this._modeMap.clear();
    }

    /**
     * @params jsonString Simple string that looks like Json file.
     */
    set string(jsonString: string) {
        this.clearAll();
        this._jsonString = jsonString;
        this.parse();
    }

    isEmpty(): Boolean {
        return this._isEmpty;
    }

    /**
     * Parsing interanl jsonString to make object.
     */
    parse = () => {
        if (this._jsonString != "") {
            console.log("parsingNewjson!");
            // clear all element in intervals list.

            this._intervalsMap.clear();
            this._propMap.clear();
            this._modeMap.clear();
            this._isEmpty = false;
            // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
            // need to take both key and value.
            console.log(this._jsonString);
            let [variable, interval, prop, mode, xdata, intervalInfo, full_interval_range] = Object.values(this._jsonString);
            this._interval_flat_list = Object.values(full_interval_range).map((e) => {
                return parseFloat(e);
            })

            // get interval info
            for (let [okey, ovalue] of Object.entries(intervalInfo)) {
                let [interval_index, interval_range, interval_data] = Object.values(ovalue);
                let tmp: IntervalInfo = {
                    intIndex: parseInt(interval_index),
                    range: Object.values(interval_range).map((e) => {
                        return parseFloat(e)
                    }),
                    data: Object.values(interval_data).map((e) => {
                        return parseFloat(e)
                    }),
                };
                this._interval_info.set(parseInt(interval_index), tmp);
            }


            // get mode
            let counter_mode = 0;
            for (let [okey, ovalue] of Object.entries(mode)) {
                let [mode_name, mode_type, mode_data] = Object.values(ovalue);
                let data = Object.values(mode_data);

                let intv_data_set: [number, number][][] = [];
                for (let ii2 = 0; ii2 < this._interval_info.size; ii2++) {
                    let numnumlist: [number, number][] = [];
                    let iifg = this._interval_info.get(ii2);
                    if (iifg) {
                        numnumlist = iifg.data.map((e) => {
                            return data[ii2] == "True" ? [e, 1] : [e, 0];
                        });
                    }
                    intv_data_set.push(numnumlist);
                }

                let tmp_mode: Mode = {
                    name: mode_name,
                    type: mode_type,
                    actual: data,
                    data: intv_data_set,
                };
                this._modeMap.set(counter_mode, tmp_mode);
                counter_mode++;
            }
            console.log(this._propMap);

            // get proposition
            let counter = 0;
            for (let [okey, ovalue] of Object.entries(prop)) {
                let [prop_name, prop_actual, prop_data] = Object.values(ovalue);
                let data = Object.values(prop_data);

                let intv_data_set: [number, number][][] = [];
                for (let ii2 = 0; ii2 < this._interval_info.size; ii2++) {
                    let numnumlist: [number, number][] = [];
                    let iifg = this._interval_info.get(ii2);
                    if (iifg) {
                        numnumlist = iifg.data.map((e) => {
                            return data[ii2] == "True" ? [e, 1] : [e, 0];
                        });
                    }
                    intv_data_set.push(numnumlist);
                }
                let tmp_prop: Proposition = {
                    name: prop_name,
                    actual: prop_actual,
                    data: intv_data_set,
                };
                this._propMap.set(counter, tmp_prop);
                counter++;
            }
            console.log(this._propMap);


            this._var_list = Object.values(variable);
            this._x_data_list = Object.values(xdata).map((s: string) => {
                return parseFloat(s)
            });
            this._graph_size = interval.length;

            for (let i = 0; i < interval.length; i++) {
                let intervals: [number, number][][] = [];
                let [index, graph, range] = Object.values(interval[i]);
                for (let [k, v] of Object.entries(graph)) {
                    let [name, intIndex, points] = Object.values(v);
                    let intIndexInt = parseInt(intIndex);

                    let tmp_interval: [number, number][] = [];
                    let varMap = this._intervalVarMap.get(intIndexInt);
                    // already exist
                    if (varMap) {
                        varMap.push(name);
                        this._intervalVarMap.set(intIndexInt, varMap);
                    } else {
                        let nVarMap = []
                        nVarMap.push(name);
                        this._intervalVarMap.set(intIndexInt, nVarMap);
                    }

                    for (let pv of points) {
                        let [x, y] = Object.values(pv);
                        tmp_interval.push([parseFloat(x), parseFloat(y)]);
                    }
                    intervals.push(tmp_interval)

                }
                let [maxX, minX, maxY, minY, m, m1, m2, m3] = Object.values(range);

                this.maxX = parseFloat(maxX);
                this.minX = parseFloat(minX);

                this._xRangeMap.set(parseInt(index), [parseFloat(minX), parseFloat(maxX)]);
                this._yRangeMap.set(parseInt(index), [parseFloat(minY), parseFloat(maxY)]);

                this._intervalsMap.set(parseInt(index), intervals);
                if (i == 0) {
                    this.totalMinX = parseFloat(minX);
                    this.totalMaxX = parseFloat(maxX);
                }
            }
            console.log(this._intervalsMap);
            console.log(this._xRangeMap);
            console.log(this._yRangeMap);
        } else {
            this._isEmpty = true;
        }
    };
}

export {Json};