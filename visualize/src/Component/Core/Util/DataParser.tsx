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
import {Intervals, Interval, Point} from "./MathModel";

/**
 * This is prop class
 */
class PropValue {

    /**
     *
     * @param _value the actual value of proposition, true or false.
     * @param _extent the extent of proposition value.
     */
    constructor(
        private _value: string = "",
        private _extent: [number, number]
    ) {
    }

    get value(): string {
        return this._value;
    }

    set value(value: string) {
        this._value = value;
    }

    get extent(): [number, number] {
        return this._extent;
    }
}

class Prop {
    private _prop_value: PropValue[] = []

    /**
     *
     * @param _name name of proposition. like "x>1".
     */
    constructor(
        private _name: string = "",
    ) {
    }

    get name(): string {
        return this._name;
    }

    set name(name: string) {
        this._name = name;
    }

    push(value: string, extent: [number, number]) {
        this._prop_value.push(new PropValue(value, extent))
    }

    get elems() {
        return this._prop_value;
    }

    includes(num: number): (string | undefined) {
        for (let el of this._prop_value) {
            if (el.extent.includes(num)) {
                return el.value;
            }
        }
        return undefined;
    }

    removeAll() {
        this._prop_value = [];
    }
}

class Props {
    private _props: Prop[] = []

    push(prop: Prop) {
        this._props.push(prop);
    }

    removeAll() {
        this._props = [];
    }

    get elems() {
        return this._props;
    }

    get names(): string[] {
        var tmp: string[] = [];
        for (let el of this._props) {
            if (!tmp.includes(el.name)) {
                tmp.push(el.name);
            }
        }
        return tmp;
    }
}

class DataList {
    // xs list only
    private _xs: number[] = [];

    // ys list only
    private _ys: number[] = [];

    constructor(
        private _name: string,
        private _value: [number, number][][]
    ) {
        this.flat();
    }

    get name() {
        return this._name;
    }

    get value() {
        return this._value;
    }

    flat() {
        for (let el of this._value) {
            for (let elem of el) {
                if (!this._xs.includes(elem[0])) {
                    this._xs.push(elem[0]);
                }
                if (!this._ys.includes(elem[1])) {
                    this._ys.push(elem[1]);
                }
            }
        }
        console.log(this._value)
        console.log(this._xs)
        console.log(this._ys)
    }

    get xs(): number[] {
        return this._xs;
    }

    get ys(): number[] {
        return this._ys;
    }
}

/**
 * Json:
 * * Wrapper class for DataGenerator project
 */
class Json {

    /**
     * Internally has intervals.
     */
    private _intervals: Intervals = new Intervals("data");
    private _isEmpty: Boolean = true;
    // TODO: This will be move to Prop class later.
    private _proposition_names: { [prop: string]: string; } = {};

    // Array of propositions. ["x>1", "x<0", ...]
    public _props: Props = new Props();

    /**
     *
     * @param _jsonString String parsing by internal json parser to string.
     */
    constructor(
        private _jsonString: string = ""
    ) {
        //...
    }

    get propNames(): string[] {
        return this._props.names;
    }

    get variables() {
        return this._intervals.names;
    }

    get data() {
        if (this._intervals.isEmpty()) {
            this.parse();
            return this._intervals;
        }
        return this._intervals;
    }

    /**
     * @params jsonString Simple string that looks like Json file.
     */
    set string(jsonString: string) {
        if (jsonString != "") {
            this._jsonString = jsonString;
            this.parse();
        }
    }

    isEmpty(): Boolean {
        return this._isEmpty;
    }

    get proposition_names() {
        return this._proposition_names;
    }

    /**
     * Parsing interanl jsonString to make object.
     */
    parse2 = () => {
        if (this._jsonString != "") {
            console.log("parsing!");
            this._intervals.removeAll();
            this._props.removeAll();
            this._isEmpty = false;
            // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
            // need to take both key and value.
            console.log(this._jsonString)
            for (let [key1, value1] of Object.entries(this._jsonString)) {
                if (key1 == "data") {
                    for (let i = 0; i < value1.length; i++) {
                        let obj = value1[i];
                        for (let [key, value] of Object.entries(obj)) {
                            let tmp_interval: Interval = new Interval(key, i);
                            for (let v of Object.values(value)) {
                                tmp_interval.push(new Point(parseFloat(v[0]), parseFloat(v[1]), key));
                            }
                            this._intervals.push(tmp_interval);
                        }
                    }
                    console.log(this._intervals)
                } else if (key1 == "proplist") {
                    //console.log("Prol"+Object.entries(value1));

                    for (let [key, value] of Object.entries(value1)) {
                        console.log("Proplist: " + value);
                        this._proposition_names[key] = value;
                    }
                }
                // for the
                else {
                    let intv_len = this._intervals.length;
                    let counter = 0;
                    let intv = this.intervalList();
                    for (let [key2, value2] of Object.entries(value1)) {
                        let tmp: Prop = new Prop(key2);
                        counter = 0;
                        for (let v of value2) {
                            if (counter != intv_len - 1) {
                                tmp.push(v, [intv[counter], intv[counter + 1]]);
                            } else {
                                tmp.push(v, [intv[intv_len - 1], intv[intv_len]]);
                            }
                            counter++;
                        }
                        this._props.push(tmp);
                    }
                }
            }
            if (this._intervals.isEmpty()) {
                this._isEmpty = true;
            }
        } else {
            this._isEmpty = true;
        }
    };


    /**
     * Parsing interanl jsonString to make object.
     */
    parse = () => {
        if (this._jsonString != "") {
            console.log("parsing2!");
            this._intervals.removeAll();
            //this._props.removeAll();
            this._isEmpty = false;
            // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
            // need to take both key and value.
            console.log(this._jsonString);
            for (let [key, value] of Object.entries(this._jsonString)) {
                if (key == "interval") {
                    for (let i = 0; i < value.length; i++) {
                        let [name, index, points] = Object.values(value[i]);
                        let tmp_interval: Interval = new Interval(name, parseInt(index));
                        for (let pv of points) {
                            let [x, y] = Object.values(pv);
                            tmp_interval.push(new Point(parseFloat(x), parseFloat(y), name));
                        }
                        this._intervals.push(tmp_interval);
                        /*for (let [key, value] of Object.entries(obj)) {
                            let tmp_interval: Interval = new Interval(key, i);
                            for (let v of Object.values(value)) {
                                tmp_interval.push(new Point(parseFloat(v[0]), parseFloat(v[1]), key));
                            }
                            this._intervals.push(tmp_interval);
                        }*/
                    }
                } else if (key == "proplist") {
                    //console.log("Prol"+Object.entries(value1));

                   /* for (let [key, value] of Object.entries(value)) {
                        console.log("Proplist: " + value);
                        this._proposition_names[key] = value;
                    }*/
                }
                // for the
                else {

                }
            }
        } else {
            this._isEmpty = true;
        }
    };



    /**
     * This will find every intervals that have id which are the same as searching parameter.
     * @params id Interval number.
     */
    dataById = (id: number): Interval[] => {
        return this._intervals.intervalById(id);
    }

    /**
     * Usually, this will be variables name.
     * @params name Interval name.
     */
    dataByName = (name: string): Interval[] => {
        return this._intervals.intervalByName(name);
    }

    /**
     * Usually, this will be variables name.
     * @params name Interval name.
     */
    dataByNameList(name: string): [number, number][][] {
        let tmp: [number, number][][] = [];
        let interv: Interval[] = this._intervals.intervalByName(name);
        for (let elem of interv) {
            if (name == elem.name) {
                tmp.push(elem.list);
            }
        }
        return tmp;
    }

    /**
     * this will replace dataList() eventually.
     */
    getDataList(): DataList[] {
        var tmp: DataList[] = [];
        for (let e of this._intervals.names) {
            tmp.push(new DataList(e, this.dataByNameList(e)))
        }
        return tmp;
    }

    /**
     * this will replace dataList() eventually.
     */
    getDataListMinor(name: string[]): DataList[] {
        var tmp: DataList[] = [];
        for (let e of this._intervals.names) {
            if (name.includes(e)) {
                tmp.push(new DataList(e, this.dataByNameList(e)))
            }
        }
        return tmp;
    }

    extentListByName(name: string): (DataList | undefined) {
        let exList = this.extentList();
        console.log(exList);
        for (let el of exList) {
            if (el.name == name) {
                return el
            }
        }
        return undefined;
    }

    extentList(): DataList[] {
        /*
        console.log(this._props.elems)
        var tmp:[number, number][][] = [];
        
        for(let el of this._intervals.elems){
            let tmp2:[number, number][] = [];
            tmp2.push([el.xExtent[0],1]);
            tmp2.push([el.xExtent[1],1]);

            // check difference, true for not same.
            let truth = 1;
            if(tmp.length != 0){
                for(let tmp_e of tmp){
                    for(let tmp_index in tmp_e){
                        if(tmp_e[tmp_index][0] == tmp2[tmp_index][0]){
                            // equal for every...
                            truth *= 0;
                        }
                        else{
                            truth *= 1;
                        }
                    }
                }
            }
            if(truth == 1)
                tmp.push(tmp2);
        }
        return tmp;*/
        /**
         * Props : list of prop.
         */
            //var tmp:[number, number][] = [];
        let tmpData: DataList[] = [];
        let tmp: [number, number][][] = [];
        for (let el in this._props.elems) {
            tmp = [];
            for (let propvals of this._props.elems[el].elems) {
                let tmp2: [number, number][] = [];
                if (propvals.value == "True") {
                    tmp2.push([propvals.extent[0], 2]);
                    tmp2.push([propvals.extent[1], 2]);
                } else {
                    tmp2.push([propvals.extent[0], 1]);
                    tmp2.push([propvals.extent[1], 1]);
                }
                tmp.push(tmp2);
            }
            //tmp.push(tmp2)
            tmpData.push(new DataList(this._props.elems[el].name, tmp))
        }
        //console.log(tmpData)
        return tmpData;
    }

    intervalList() {
        var tmp: number[] = [];
        // assert that parse being called before this function.
        //this.parse();
        for (let e of this._intervals.names) {
            let interv: Interval[] = this._intervals.intervalByName(e);
            for (let el of interv) {
                var min = el.xMin;
                var max = el.xMax;
                if (tmp.includes(max)) {

                } else if (tmp.includes(min)) {

                } else {
                    if (min == max) {
                        tmp.push(min);
                    } else {
                        tmp.push(min);
                        tmp.push(max);
                    }
                }
            }
        }
        return tmp;
    }

    /**
     * Reset every data structure.
     */
    reset() {
        this._intervals.removeAll();
        this._isEmpty = true;
        this._proposition_names = {};
        this._props.removeAll();
        this._jsonString = "";
    }
}

/**
 * WorkspaceJson:
 * * Wrapper class for DataGenerator project
 */
class WorkspaceJson {

    // _file_list will be deprecated
    private _file_list: string[] = [];
    private _file_list_map: Map<number, string> = new Map<number, string>();

    /**
     *
     * @param _jsonString String parsing by internal json parser to string.
     */
    constructor(
        private _jsonString: string = ""
    ) {
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for (let [key1, value1] of Object.entries(this._jsonString)) {
            if (key1 == "file_list") {
                for (let i = 0; i < value1.length; i++) {
                    let obj = value1[i];
                    this._file_list.push(obj);
                }
            } else {
                console.log("Workspace error!")
            }
        }
    };

    load(jsonString: string = ""){
        this._file_list = [];
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for (let [key1, value1] of Object.entries(this._jsonString)) {
            if (key1 == "file_list") {
                for (let i = 0; i < value1.length; i++) {
                    let obj = value1[i];
                    this._file_list.push(obj);
                }
            } else {
                console.log("Workspace error!")
            }
        }
    }

    add(uid: number, title:string){
        this._file_list_map.set(uid, title);
    }

    clear(){
        this._file_list_map.clear();
    }

    get file_list() {
        return this._file_list;
    }

    get flist() {
        this._file_list = [];
        this._file_list_map.forEach((v: string, _:number)=>{
            this._file_list.push(v);
        })
        return this._file_list;
    }
}

export {Json, WorkspaceJson};