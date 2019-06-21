/**
 * Data class for mathematical objects
 * Json should follow this format
 */
export interface point{
    name: string;
    point_list: ptype;
}
// list of points
export type ptype = (plist | pelem)
export type points = point[][];
export type pointsElem = point[];
export type pelem = number[];
export type plist = pair[];
export type json = string;
export type pair = [number, number];


export class DataManager {
    private _p:points=[[]];
    private _x:points=[[]];
    private _y:points=[[]];
    private _p_elem:pointsElem=[];
    private _variables:string[]=[];
    constructor(
        private _data: json=''
    ){}
    get data(): json{
        return this._data;
    }
    set data(d: json){
        this._data = d;
        this.update();
        this.updateX();
        this.updateY();
        this.updateVariables();
    }

    // update this function will effect every thing that is related with
    // this._data 
    //  e.g) updateX and updateY will be affected by changing
    // parseFloat(v[0]*100)...
    update(){
        this._p = [[]];
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let i=0; i<this._data.length;i++){
            let obj = this._data[i];
            for(let [key, value] of Object.entries(obj)){
                let tmp_point_list:[number, number][] = [];
                for (let v of Object.values(value)){
                    tmp_point_list.push([parseFloat(v[0]), parseFloat(v[1])]);
                }
                this._p_elem.push({name:key, point_list: tmp_point_list});
            }
            //this._p_elem.shift();
            this._p.push(this._p_elem);
            this._p_elem = [];
        }
        this._p.shift();
    }

    updateX(){
        this._x = [];
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let i=0; i<this._data.length;i++){
            let obj = this._data[i];
            for(let [key, value] of Object.entries(obj)){
                let tmp_point_list:number[] = [];
                for (let v of Object.values(value)){
                    tmp_point_list.push(parseFloat(v[0]));
                }
                this._p_elem.push({name:key, point_list: tmp_point_list});
            }
            //this._p_elem.shift();
            this._x.push(this._p_elem);
            this._p_elem = [];
        }
        //this._x.shift();
    }

    updateY(){
        this._y = [];
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let i=0; i<this._data.length;i++){
            let obj = this._data[i];
            for(let [key, value] of Object.entries(obj)){
                let tmp_point_list:number[] = [];
                for (let v of Object.values(value)){
                    tmp_point_list.push(parseFloat(v[1]));
                }
                this._p_elem.push({name:key, point_list: tmp_point_list});
            }
            //this._p_elem.shift();
            this._y.push(this._p_elem);
            this._p_elem = [];
        }
        //this._y.shift();
    }

    // mode can change variables????
    // assumes not...
    updateVariables(){
        this._variables = [];
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let i=0; i<this._data.length;i++){
            let obj = this._data[i];
            for(let [key, value] of Object.entries(obj)){
                if (this._variables.includes(key)){
                    // do nothing
                }
                else{
                    this._variables.push(key);
                }
            }
        }
    }

    get variables():string[]{
        return this._variables;
    }

    get points():points{
        return this._p;
    }

    get x(){
        return this._x;
    }

    get y(){
        return this._y;
    }
}