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
import { Intervals, Interval, Point } from "../Core/Util/MathModel";

/**
 * This is prop class
 */
class PropValue{

    /**
     * 
     * @param _value the actual value of proposition, true or false.
     * @param _extent the extent of proposition value.
     */
    constructor(
        private _value:string="",
        private _extent:[number, number]
        ){}

    get value():string{
        return this._value;
    }

    set value(value: string){
        this._value = value;
    }

    get extent():[number, number]{
        return this._extent;
    }
}

class Prop{
    private _prop_value:PropValue[] = []

    /**
     * 
     * @param _name name of proposition. like "x>1".
     */
    constructor(
        private _name:string="",
    ){}

    get name():string{
        return this._name;
    }

    set name(name:string){
        this._name = name;
    }

    push(value:string, extent:[number, number]){
        this._prop_value.push(new PropValue(value, extent))
    }

    get elems(){
        return this._prop_value;
    }

    includes(num:number):(string | undefined) {
        for(let el of this._prop_value){
            if(el.extent.includes(num)){
                return el.value;
            }
        }
        return undefined;
    }

    removeAll(){
        this._prop_value = [];
    }
}

class Props{
    private _props: Prop[] = []

    push(prop:Prop){
        this._props.push(prop);
    }

    removeAll(){
        this._props=[];
    }

    get elems(){
        return this._props;
    }

    get names(): string[]{
        var tmp: string[] = [];
        for(let el of this._props){
            if(!tmp.includes(el.name)){
                tmp.push(el.name);
            }
        }
        return tmp;
    }
}

class DataList{
    constructor(
        private _name: string,
        private _value: [number, number][][]
    ){}

    get name(){
        return this._name;
    }

    get value(){
        return this._value;
    }
}

 /**
  * Json:
  * * Wrapper class for visualize project
  */
class Json {

    /**
     * Internally has intervals.
     */
    private _intervals: Intervals = new Intervals("data");

    // Array of propositions. ["x>1", "x<0", ...]
    public _props:Props = new Props();
    /**
     * 
     * @param _jsonString String parsing by internal json parser to string.
     */
    constructor(
        private _jsonString:string = ""
    ){
        //...
    }

    get propNames(): string[]{
        return this._props.names;
    }

    get names(){
        return this._intervals.names;
    }

    get data(){
        if(this._intervals.isEmpty()){
            this.parse();
            return this._intervals;
        }
        return this._intervals;
    }

    /**
     * @params jsonString Simple string that looks like Json file.
     */
    set string(jsonString:string){
        this._jsonString = jsonString;
        this.parse();
    }

    /**
     * Parsing interanl jsonString to make object.
     */
    parse = () => {
        this._intervals.removeAll();
        this._props.removeAll();
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let [key1, value1] of Object.entries(this._jsonString)){
            if(key1=="data"){
                for(let i=0; i<value1.length;i++){
                    let obj = value1[i];
                    for(let [key, value] of Object.entries(obj)){
                        let tmp_interval:Interval = new Interval(key, i);
                        for (let v of Object.values(value)){
                            tmp_interval.push(new Point(parseFloat(v[0]), parseFloat(v[1]), key));
                        }
                        this._intervals.push(tmp_interval);
                    }
                }
            }
            // for the 
            else{
                let intv_len = this._intervals.length
                let counter = 0
                let intv = this.intervalList();
                for(let [key2, value2] of Object.entries(value1)){
                    let tmp: Prop = new Prop(key2)
                    for(let v of value2){
                        if(counter != intv_len-1){
                            tmp.push(v, [intv[counter], intv[counter+1]])
                        }
                        counter++;
                    }
                    this._props.push(tmp)
                }
                console.log(this._props);
            }
        }
    }

    /**
     * This will find every intervals that have id which are the same as searching parameter.
     * @params id Interval number.
     */
    dataById = (id:number):Interval[] => {
        return this._intervals.intervalById(id);
    }

    /**
     * Usually, this will be variables name.
     * @params name Interval name.
     */
    dataByName = (name:string):Interval[] => {
        return this._intervals.intervalByName(name);
    }

    /**
     * Usually, this will be variables name.
     * @params name Interval name.
     */
    dataByNameList(name:string):[number, number][][]{
        let tmp: [number, number][][] = [];
        let interv:Interval[] = this._intervals.intervalByName(name);
        for(let elem of interv){
            if(name==elem.name){
                tmp.push(elem.list);
            }
        }
        return tmp;
    }

    /**
     * this will replace dataList() eventually.
     */
    getDataList(): DataList[]{
        var tmp: DataList[] = [];
        for(let e of this._intervals.names){
            tmp.push(new DataList(e, this.dataByNameList(e)))
        }
        return tmp;
    }

    /**
     * Get data List item... update... later..
     */
    dataList():[number, number][][]{
        var tmp: [number, number][][] = [];
        for(let e of this._intervals.names){
            tmp.push(this.dataByNameList(e).flat());
        }
        return tmp;
    }

    extentList(){
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
        return tmp;
    }

    intervalList(){
        var tmp: number[] = [];
        // assert that parse being called before this function.
        //this.parse();
        for(let e of this._intervals.names){
            let interv:Interval[] = this._intervals.intervalByName(e);
            for(let el of interv){
                var min = el.xMin;
                var max = el.xMax;
                if (tmp.includes(max)){

                }
                else if (tmp.includes(min)){

                }
                else{
                    if(min==max){
                        tmp.push(min);
                    }
                    else{
                        tmp.push(min);
                        tmp.push(max);
                    }
                }
            }
        }
        return tmp;
    }
}

export { Json };