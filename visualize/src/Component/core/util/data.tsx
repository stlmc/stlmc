/**
 * Data class for mathematical objects
 * Json should follow this format
 */
export type data = [number, number][];
export class DataManager {
    constructor(
        private _data: data=[[0,0]]
    ){}

    get data(): data{
        return this._data;
    }
    set data(d: data){
        this._data = d;
    }
    get x():number[]{
        let pd: number[] = []
        for(let index in this._data){
            pd.push(this._data[index][0]);
            //pd.push(this._data[index].x);
        }
        return pd;
    }

    get y():number[]{
        let pd: number[] = [];
        for(let index in this._data){
            pd.push(this._data[index][1]);
        }
        return pd;
    }
}