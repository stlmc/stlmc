/**
 * Basic class for *mathematical* **object**.
 * This class contains single point *(x, y)* class, interval class.
 *  
 * Written by Geunyeol Ryu
 * @ 2019.06.06
 */

 /**
 * Point:
 * * Single point consists of pair of x and y with its own name.
 * * It has polymorphic type T and U.
 * * example:
 *   > type T for number type and  type U for string
 *   > (x, y)
 *   > called this point as "x_1"
 * @typeparam T the point's value type. Default type is number.
 * @typeparam U the point's name type. Default type is string.
 */
class Point<T=number, U=string>{

    /**
     * 
     * @param _x The first element of the point.
     * @param _y The second element of the point.
     * @param _name Also known as nickname, name of the point.
     */
    constructor(
        private _x:T,
        private _y:T,
        private _name: U,
    ){
        // feel free to update.
    }

    /**
     * Get name of point.
     */
    get name():U{
        return this._name;
    }

    /**
     * Set name of point.
     */
    set name(name:U){
        this._name = name;
    }

    /**
     *  Get first element of the point.
     * @returns T type value x.
     */
    get x():T{
        return this._x;
    }

    /**
     * Set the first element of the point.
     * @param x The value you want for the point to have.
     */
    set x(x:T){
        this._x = x;
    }

    /**
     * Get second element of the point.
     * @returns T type value y.
     */
    get y():T{
        return this._y;
    }

    /**
     * Set second element of the point.
     * @param y The value you want for the point to have.
     */
    set y(y:T){
        this._y = y;
    }

    /**
     * Get both element of the point.
     */
    get pair():[T, T]{
        return [this._x, this._y];
    }
}

 /**
 * Interval:
 * * Array of points with name.
 * * It has polymorphic type T and U same as point class.
 * * example:
 *   > type T for number type and  type U for string
 *   > [(x, y), (x_1, y_1) ... ]
 *   > called this interval as "interval_1"
 * @typeparam V the array's name type. Default type is string.
 * @typeparam T the array's point value type. Default type is number. 
 * @typeparam U the array's point name type. Default type is string.
 */
class Interval<V=string, T=number, U=string>{

    /**
     * Interval's inner point's array. Empty at first time.
     */
    private _points: Point<T, U>[] = [];

    /**
     * 
     * @param _name The interval's name
     * @param _id Unique interval's id. Mostly used as index of intervals.
     */
    constructor(
        private _name:V,
        private _id: number
        ){
        // feel free to update ...
    }

    /**
     * Get id of interval.
     */
    get id():number{
        return this._id;
    }

    /**
     * Set id of interval.
     */
    set id(id:number){
        this._id = id;
    }

    /**
     * Appends new elements to an array, and returns the new length of the array.
     * @param items New elements of the Array.
     */
    push(item: Point<T, U>): number{
        return this._points.push(item);
    }

    /**
     * Removes the last element from an array and returns it.
     */
    pop(): Point<T, U> | undefined{
        return this._points.pop();
    }

    /**
     * Get name of the interval.
     */
    get name(): V{
        return this._name;
    }

    /**
     * Get array of points' names. This method will automatically remove overlapping names.
     */
    get names(): U[]{
        var tmp:U[] = [];
        for(let elem of this._points){
            if(tmp.includes(elem.name)){
                // do nothing...
            }else{
                tmp.push(elem.name);
            }
        }
        return tmp;
    }

    /**
     * Get array of points' xs.
     */
    get x():T[]{
        var tmp:T[] = [];
        for(let elem of this._points){
            tmp.push(elem.x);
        }
        return tmp;
    }

    /**
     * Get array of points' ys.
     */
    get y(){
        var tmp:T[] = [];
        for(let elem of this._points){
            tmp.push(elem.y);
        }
        return tmp;
    }

    /**
     * Get point's pairs list.
     */
    get list(){
        var tmp: [T, T][] = [];
        for(let elem of this._points){
            tmp.push(elem.pair);
        }
        return tmp;
    }

    /**
     * Helper method for extent x and y.
     */
    private extent = (isX:boolean):[Point<T, U>, Point<T, U>] => {
        if(isX){
            var max:Point<T,U> = this._points.reduce(
                (acc, cur) => {
                    return acc.x > cur.x ? acc:cur;
                })

            var min:Point<T,U> = this._points.reduce(
                (acc, cur) => {
                    return acc.x > cur.x ? cur:acc;
                })
            return [min, max]
        }
        else{
            var max:Point<T,U> = this._points.reduce(
                (acc, cur) => {
                    return acc.y > cur.y ? acc:cur;
                })

            var min:Point<T,U> = this._points.reduce(
                (acc, cur) => {
                    return acc.y > cur.y ? cur:acc;
                })
            return [min, max]
        }
    }

    /**
     * Get extent of interval's xs.
     * @returns Tuple of min and max value of the points' first elements.
     */
    get xExtent():[T, T] { 
        var extent:[Point<T, U>, Point<T, U>] = this.extent(true);
        return [extent[0].x, extent[1].x];
    }

    /**
     * Get extent of interval's ys.
     * @returns Tuple of min and max value of the points' second elements.
     */
    get yExtent():[T, T] {
        var extent:[Point<T, U>, Point<T, U>] = this.extent(false);
        return [extent[0].y, extent[1].y];
    }

    /**
     * Get max value of interval's xs.
     * @returns Max value of the points' first elements.
     */
    get xMax():T {
        var extent:[Point<T, U>, Point<T, U>] = this.extent(true);
        return extent[1].x;
    }

    /**
     * Get min value of interval's xs.
     * @returns Min value of the points' first elements.
     */
    get xMin() {
        var extent:[Point<T, U>, Point<T, U>] = this.extent(true);
        return extent[0].x;
    }

    /**
     * Get max value of interval's ys.
     * @returns Max value of the points' second elements.
     */
    get yMax() {
        var extent:[Point<T, U>, Point<T, U>] = this.extent(false);
        return extent[1].y;
    }

    /**
     * Get min value of interval's ys.
     * @returns Min value of the points' second elements.
     */
    get yMin() {
        var extent:[Point<T, U>, Point<T, U>] = this.extent(false);
        return extent[0].y;
    }

}

 /**
 * Intervals:
 * * Array of Interval with name. 
 * * It's element, interval has polymorphic type V, T and U.
 * 
 * @typeparam W the array of Interval name's type. Default type is string.
 * @typeparam V the element, Interval name's type. Default type is string.
 * @typeparam T the element, Interval's point value type. Default type is number.
 * @typeparam U the elemet, Interval's point name type. Default type is string.
 */
class Intervals<W=string, V=string, T=number, U=string> {
    private _intervals: Interval<V,T,U>[] = [];
    
    /**
     * 
     * @param _name The intervals name.
     */
    constructor(
        private _name: W
    ){}

    /**
     * Get intervals.
     */
    get elems():Interval<V,T,U>[]{
        return this._intervals;
    }

    /**
     * Length of array of interval.
     * 
     * @returns Actual length of array of interval with duplicate interval id removal.
     */
    get length():number{
        var id_list:number[] = []
        for(let el of this._intervals){
            if(id_list.includes(el.id)){

            }
            else{
                id_list.push(el.id)
            }
        }
        return id_list.length;
    }

    /**
     * Array of the interval to array of [T, T] type.
     * 
     * @deprecated This method will be deprecated soon.
     * @todo Redesigning this method to return any array.
     * @returns It will return [T, T][][] type list.
     */
    toTTList():[T, T][][]{
        var tmp: [T, T][][] = [];
        for(let elem of this._intervals){
            tmp.push(elem.list);
        }
        return tmp;
    }

    /**
     * Appends new elements to an array, and returns the new length of the array.
     * @param items New elements of the Array.
     */
    push(item: Interval<V, T, U>): number{
        return this._intervals.push(item);
    }

    /**
     * Removes the last element from an array and returns it.
     */
    pop(): Interval<V, T, U> | undefined{
        return this._intervals.pop();
    }

    /**
     * Remove all elements from the array.
     */
    removeAll(){
        this._intervals = [];
    }

    /**
     * Check if the array is empty.
     */
    isEmpty(){
        return this._intervals.length == 0;
    }


    /**
     * Name of this array of interval.
     */
    get name(): W{
        return this._name;
    }

    /**
     * Array of interval's names. Names will automatically does not count overlapping names.
     * 
     * @returns Array of names. 
     */
    get names(): V[]{
        var tmp:V[] = [];
        for(let elem of this._intervals){
            if(tmp.includes(elem.name)){
                // do nothing...
            }else{
                tmp.push(elem.name);
            }
        }
        return tmp;
    }

    /**
     * Get certain intervals that has certain name. There might be some numbers of intervals.
     * 
     * @param name Name that you expect for Intervals to have.
     * @returns Array of intervals that matches naming condition.
     */
    intervalByName(name:V): Interval<V, T, U>[]{
        var tmp: Interval<V, T, U>[] = [];
        for(let elem of this._intervals){
            if(elem.name==name){
                tmp.push(elem);
            }
        }
        return tmp;
    }

    /**
     * Get certain intervals that has certain id. There might be some numbers of intervals.
     * 
     * @param id Unique id that you expect for Intervals to have.
     * @returns Array of intervals that matches above condition.
     */
    intervalById(id:number): Interval<V, T, U>[]{
        var tmp: Interval<V, T, U>[] = [];
        for(let elem of this._intervals){
            if(elem.id==id){
                tmp.push(elem);
            }
        }
        return tmp;
    }

    /**
     * Get range of intervals of the first element with certain name.
     * 
     * @param name Name of the interval that you want to get range.
     * @returns Range of intervals.
     */
    xRangeByName(name:V):[T, T]{
        var tmp:[T, T][] = [];
        for(let elem of this.intervalByName(name)){
            tmp.push(elem.xExtent);
        }

        var tmp_flat:T[] = tmp.flat();

        var max = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? acc:cur;
            }
        )

        var min = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? cur:acc;
            }
        )
        return [min, max];
    }

    /**
     * Get range of intervals of the second element with certain name.
     * 
     * @param name Name of the interval that you want to get range.
     * @returns Range of intervals.
     */
    yRangeByName(name:V):[T, T]{
        var tmp:[T, T][] = [];
        for(let elem of this.intervalByName(name)){
            tmp.push(elem.yExtent);
        }

        var tmp_flat:T[] = tmp.flat();

        var max = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? acc:cur;
            }
        )

        var min = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? cur:acc;
            }
        )
        return [min, max];
    }

    /**
     * Get range of intervals of the first element with certain id.
     * 
     * @param id Unique id of the interval that you want to get range.
     * @returns Range of intervals.
     */
    xRangeById(id:number):[T, T]{
        var tmp:[T, T][] = [];
        for(let elem of this.intervalById(id)){
            tmp.push(elem.xExtent);
        }

        var tmp_flat:T[] = tmp.flat();

        var max = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? acc:cur;
            }
        )

        var min = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? cur:acc;
            }
        )
        return [min, max];
    }

    /**
     * Get range of intervals of the second element with certain id.
     * 
     * @param id Unique id of the interval that you want to get range.
     * @returns Range of intervals.
     */
    yRangeById(id:number):[T, T]{
        var tmp:[T, T][] = [];
        for(let elem of this.intervalById(id)){
            tmp.push(elem.yExtent);
        }

        var tmp_flat:T[] = tmp.flat();

        var max = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? acc:cur;
            }
        )

        var min = tmp_flat.reduce(
            (acc, cur) => {
                return acc > cur? cur:acc;
            }
        )
        return [min, max];
    }

    /**
     * Get range this Intervals with respect to the first element. 
     * This will return whole range of whole Intervals.
     * 
     * @returns First element's range of this Intervals.
     */
    xRange():[T, T]{
        var tmp:[T, T][] = []; 
        for(let e of this._intervals){
            let t = this.xRangeByName(e.name).flat();
            let max = t.reduce(
                (acc, cur) => {
                    return acc > cur? acc:cur;
                }
            )
    
            let min = t.reduce(
                (acc, cur) => {
                    return acc > cur? cur:acc;
                }
            )
            tmp.push([min, max]);
        }
        let arr = tmp.flat();
        let max = arr.reduce(
            (acc, cur) => {
                return acc > cur? acc:cur;
            }
        )

        let min = arr.reduce(
            (acc, cur) => {
                return acc > cur? cur:acc;
            }
        )
        return [min, max];
    }

    /**
     * Get range this Intervals with respect to the second element. 
     * This will return whole range of whole Intervals.
     * 
     * @returns Second element's range of this Intervals.
     */
    yRange():[T, T]{
        var tmp:[T, T][] = []; 
        for(let e of this._intervals){
            let t = this.yRangeByName(e.name).flat();
            let max = t.reduce(
                (acc, cur) => {
                    return acc > cur? acc:cur;
                }
            )
    
            let min = t.reduce(
                (acc, cur) => {
                    return acc > cur? cur:acc;
                }
            )
            tmp.push([min, max]);
        }
        let arr = tmp.flat();
        let max = arr.reduce(
            (acc, cur) => {
                return acc > cur? acc:cur;
            }
        )

        let min = arr.reduce(
            (acc, cur) => {
                return acc > cur? cur:acc;
            }
        )
        return [min, max];
    }
}

export { Point, Interval, Intervals };