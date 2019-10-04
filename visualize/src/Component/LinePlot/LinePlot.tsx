import React from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import './style/LinePlotStyle.scss';
import '../../Style/scss/main.scss';
import {Intervals, margin, size} from '../Core/Util/Util';
import {Renderer} from '../Core/Renderer/MainRenderer';
import {PropositionRenderer} from '../Core/Renderer/PropositionRenderer';
import {Json, NewJson, WorkspaceJson} from '../Core/Util/DataParser';
import Select from 'react-select';
import {ActionMeta, ValueType} from 'react-select/src/types';
import {Tab, Tabs, TabList, TabPanel} from 'react-tabs';
import "react-tabs/style/react-tabs.css";
import Axios, {AxiosInstance} from "axios";
import { Button, Form, Toast } from 'react-bootstrap';



/*
 * Props and State
 */
interface Props {
}

interface Popup {
    isEnabled: boolean;
}

interface WorkspaceData {
    title: string;
    uid: number;
}

interface ServerError {
    message: string;
    error: boolean;
}



interface State {
    popup: Popup;
    selectedVariables: string[];
    allVariables: string[];
    isRedraw: boolean;
    model: WorkspaceData[];
    graphNum : number;
    xlist: number[];
    selectedProps: string[];
    allProps: string[];
    toggle: Map<number, boolean>;
    isToggleChanged: boolean;

    serverError: ServerError;
}

/*
 * LinePlot Component
 * no longer need constructors
 * https://medium.com/@martin_hotell/react-typescript-and-defaultprops-dilemma-ca7f81c661c7
 */
class LinePlot extends React.Component<Props, State> {

    private width: number = parseFloat(styleVariable.width.replace("px", ""));
    private height: number = parseFloat(styleVariable.height.replace("px", ""));
    private width_viewer: number = parseFloat(styleVariable.width_viewer.replace("px", ""));
    private height_viewer: number = parseFloat(styleVariable.height_viewer.replace("px", ""));
    private width_controller: number = parseFloat(styleVariable.width_controller.replace("px", ""));
    private height_controller: number = parseFloat(styleVariable.height_controller.replace("px", ""));

    private margin_viewer_top: number = parseFloat(styleVariable.margin_viewer_top.replace("px", ""));
    private margin_viewer_right: number = parseFloat(styleVariable.margin_viewer_right.replace("px", ""));
    private margin_viewer_bottom: number = parseFloat(styleVariable.margin_viewer_bottom.replace("px", ""));
    private margin_viewer_left: number = parseFloat(styleVariable.margin_viewer_left.replace("px", ""));

    private margin_controller_top: number = parseFloat(styleVariable.margin_controller_top.replace("px", ""));
    private margin_controller_right: number = parseFloat(styleVariable.margin_controller_right.replace("px", ""));
    private margin_controller_bottom: number = parseFloat(styleVariable.margin_controller_bottom.replace("px", ""));
    private margin_controller_left: number = parseFloat(styleVariable.margin_controller_left.replace("px", ""));

    private renderer: Renderer = new Renderer(
        new size(
            this.width,
            this.height,
            this.width_viewer,
            this.height_viewer,
            this.width_controller,
            this.height_controller
        ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "#graph"
    );


    private renderers: Renderer[] = [];
    private propRenderers: PropositionRenderer[] = [];
    private instance: AxiosInstance;

    private propRenderer: PropositionRenderer = new PropositionRenderer(
        new size(
            this.width,
            this.height,
            this.width_viewer,
            this.height_viewer,
            this.width_controller,
            this.height_controller
        ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "#graph"
    );

    private propRenderer2: PropositionRenderer = new PropositionRenderer(
        new size(
            this.width,
            this.height,
            this.width_viewer,
            this.height_viewer,
            this.width_controller,
            this.height_controller
        ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "#graph",
        1
    );


    private json = new Json("");
    private njson = new NewJson();

    // this will get error if change './data/test.json' to this.props.jsonpath
    state: State = {
        popup: {
            isEnabled: true,
        },
        selectedVariables: [],
        allVariables: [],
        isRedraw: false,
        graphNum: 0,
        model: [],
        selectedProps: [],
        allProps: [],
        toggle: new Map<number, boolean>(),
        isToggleChanged: false,
        xlist: [],
        serverError: {
            message: "",
            error: false,
        }
    };

    constructor(props: Props) {
        super(props);

        // Set config defaults when creating the instance

        this.onPopupChange = this.onPopupChange.bind(this);
        this.onPopupClick = this.onPopupClick.bind(this);
        this.onPropSelect = this.onPropSelect.bind(this);
        this.onModelListSelect = this.onModelListSelect.bind(this);
        this.onVariablesChange = this.onVariablesChange.bind(this);
        this.onResetButtonClick = this.onResetButtonClick.bind(this);
        this.instance = Axios.create({baseURL: 'http://localhost:3001'});
        this.toggler = this.toggler.bind(this);
        this.Item = this.Item.bind(this);
        this.ItemList = this.ItemList.bind(this);
        this.ErrorToast = this.ErrorToast.bind(this);
    }

    async componentDidMount() {

        console.log("ComponentDidMount");

        // get file_list
        await this.instance.get(`/file_list`)
            .catch((error)=>{
                console.log(error);
                this.setState({
                    serverError: {
                        error: true,
                        message: error,
                    }
                })
            }).then((response)=>{
                if (response){
                    this.setState({
                        selectedVariables: this.json.variables,
                        allVariables: this.json.variables,
                        isRedraw: false,

                        model:
                            response.data.file_list.map((v:string) => {
                                let [title, uid] = Object.values(v);
                                let workspace: WorkspaceData = {
                                    title: title,
                                    uid: parseInt(uid),
                                };
                                return workspace;
                            }),
                        selectedProps: this.json.propNames,
                        allProps: this.json.propNames,
                    })
                }
            })
        // must invoke setdata() before draw()
        //this.renderer.setdata(this.json);

        //this.propRenderer.setdata(this.json);
        //this.propRenderer2.setdata(this.json);



    }

    componentDidUpdate(prevProps: Readonly<Props>, prevState: Readonly<State>, snapshot?: any): void {
        console.log("componentDidUpdate");

        /*this.renderer.selectedVariables = this.state.selectedVariables;
        this.renderer.graphMap = this.state.graph;

        console.log(this.state.isRedraw);
        // redraw whole thing.
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0], this.state.isRedraw);
        this.renderer.resize(this.json.propNames.length);
        */
        if (this.state.serverError.error){
            this.setState({
                serverError: {
                    error: false,
                    message: "",
                }
            });
        }

        console.log("come on " + this.renderers.length)

        for (let e = 0; e < this.renderers.length; e++) {
            console.log(e);
            let intv: ([number, number][][] | undefined) = this.njson.GetGraph(e);
            if (intv) {
                this.renderers[e].loadGraph("", this.state.isRedraw, this.njson.xRange(e), this.njson.yRange(e), intv, this.state.xlist);
            }
        }



        //this.propRenderer.reload(this.json.isEmpty(), this.json.propNames[0], this.state.isRedraw);
        //this.propRenderer2.reload(this.json.isEmpty(), this.json.propNames[1], this.state.isRedraw);
        /*for (let e = 0; e < this.state.selectedProps.length; e++) {
            this.propRenderers[e].reload(this.json.isEmpty(), this.state.selectedProps[e], this.state.isRedraw);
        }*/
    }

    onPopupChange(e: React.ChangeEvent<HTMLInputElement>) {
    }

    onPopupClick(e: React.MouseEvent<HTMLInputElement, MouseEvent>) {
        this.setState({
            popup: {
                isEnabled: e.currentTarget.checked
            }
        }, () => {
            this.renderer.updatePopup(this.state.popup.isEnabled)
        });
        console.log("mouse event");
        console.log(this.state)
    }

    onPropSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {
        //this.renderer.redrawPropCanvas((value2 as { value: string, label: string; })["value"]);
        console.log(`action: ${actionMeta.action}`);
        let target = (value2 as ({ value: string; label: string; }[]));

        let tmp: string[] = [];
        if (target) {
            for (let el of target) {
                tmp.push(el["value"])
            }
        }
        if (actionMeta.action == "remove-value") {
            this.setState({
                selectedProps: tmp,
            });
        } else if (actionMeta.action == "select-option") {
            this.setState({
                selectedProps: tmp,
            });
        } else if (actionMeta.action == "clear") {
            this.setState({
                selectedProps: [],
            });
        }
    }

    async onModelListSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {


        let mapIterator = this.state.model.entries();
        let titleVal =  (value2 as { value: string; label: string; })["value"];

        console.log("onModelList... " + titleVal);

        let ws = this.state.model.find((value, index) => value.title == titleVal);
        console.log(ws);

        // if id exists.
        if (ws != undefined) {
            let response = await this.instance.get("/file/" +ws.uid);
            console.log(response.data);

            this.njson.string = response.data;
            console.log(this.njson.variables);
            let gs = this.njson.GetGraphSize();
            console.log("GraphSize is "+ gs);
            this.renderers = []
            for (let e = 0; e < gs; e++) {
                let red = new Renderer(
                    new size(
                        this.width,
                        this.height,
                        this.width_viewer,
                        this.height_viewer,
                        this.width_controller,
                        this.height_controller
                    ),
                    new margin(
                        this.margin_viewer_top,
                        this.margin_viewer_right,
                        this.margin_viewer_bottom,
                        this.margin_viewer_left
                    ),
                    new margin(
                        this.margin_controller_top,
                        this.margin_controller_right,
                        this.margin_controller_bottom,
                        this.margin_controller_left
                    ),
                    // need to concat . before string of className for d3.js
                    // https://www.tutorialspoint.com/d3js/d3js_selections.htm
                    e
                );
                red.graph = this.njson.GetGraph(e);
                console.log(red.graph);
                this.renderers.push(red);
            }

            //this.renderer.setdata(this.json);
/*
            this.propRenderers = [];
            for (let e = 0; e < this.json.propNames.length; e++) {
                let pr = new PropositionRenderer(
                    new size(
                        this.width,
                        this.height,
                        this.width_viewer,
                        this.height_viewer,
                        this.width_controller,
                        this.height_controller
                    ),
                    new margin(
                        this.margin_viewer_top,
                        this.margin_viewer_right,
                        this.margin_viewer_bottom,
                        this.margin_viewer_left
                    ),
                    new margin(
                        this.margin_controller_top,
                        this.margin_controller_right,
                        this.margin_controller_bottom,
                        this.margin_controller_left
                    ),
                    // need to concat . before string of className for d3.js
                    // https://www.tutorialspoint.com/d3js/d3js_selections.htm
                    "#graph",
                    e
                );
                pr.setdata(this.json);
                this.propRenderers.push(pr);
            }
*/
            //this.propRenderer.setdata(this.json);
            //this.propRenderer2.setdata(this.json);
            // get reloaded new variables.
            for (let i = 0; i < this.njson.GetGraphSize(); i++) {
                this.state.toggle.set(i, true);
            }

            this.setState({
                allVariables: this.json.variables,
                selectedVariables: this.json.variables,
                isRedraw: false,
                graphNum: this.njson.GetGraphSize(),
                xlist: this.njson.xlist,
                allProps: this.json.propNames,
                selectedProps: this.json.propNames,
            });
        }
    }

    // onff = () => {
    //    this.setOpen(!this.open)
    // }

    // This will get multiple choices.
    onVariablesChange(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {
        console.log(`action: ${actionMeta.action}`);
        let target = (value2 as ({ value: string; label: string; }[]));

        let tmp: string[] = [];
        if (target) {
            for (let el of target) {
                tmp.push(el["value"])
            }
        }
        if (actionMeta.action == "remove-value") {
            this.setState({
                selectedVariables: tmp,
                isRedraw: true,
            });
        } else if (actionMeta.action == "select-option") {
            this.setState({
                selectedVariables: tmp,
                isRedraw: true,
            });
        } else if (actionMeta.action == "clear") {
            this.setState({
                selectedVariables: [],
                isRedraw: true,
            });
        }
    }

    // https://stackoverflow.com/questions/23450534/how-to-call-a-python-function-from-node-js
    async onResetButtonClick(){
        console.log("reset called");
        let response = await this.instance.get(`/file_list`);
        //console.log(v);
        this.setState({
            model:
                response.data.file_list.map((v:string) => {
                    let [title, uid] = Object.values(v);
                    let workspace: WorkspaceData = {
                        title: title,
                        uid: parseInt(uid),
                    };
                    return workspace;
                }),
        })
    }

    toggler(e: React.MouseEvent<HTMLInputElement, MouseEvent>) {
        console.log("toggler");
        let r = this.state.toggle.get(0);
        console.log(r);
        if (r == false){
            this.setState({
                toggle:
                    this.state.toggle.set(0, true)
            });

        } else {
            this.setState({
                toggle:
                    this.state.toggle.set(0, false)
            });
        }
    }

    Item(index: number){

        return (
            <Form.Row>
                <Form.Check
                    label={`Enabled it`}
                    checked={this.state.toggle.get(index)}
                    onClick={() => {
                        let r = this.state.toggle.get(index);
                        console.log(this.state.toggle);
                        if (r == false) {
                            this.setState({
                                isToggleChanged: true,
                                toggle:
                                    this.state.toggle.set(index, true)
                            });

                        } else {
                            this.setState({
                                isToggleChanged: true,
                                toggle:
                                    this.state.toggle.set(index, false)
                            });
                        }
                    }
                    }
                />
                <Form.Row>
                    <div className="svg_div" id={"graph"+index} style={{display: this.state.toggle.get(index) ? 'block' : 'none' }}>
                        <span></span>
                    </div>
                </Form.Row>
            </Form.Row>
        )
    }

    ItemList(){
        let res = [];
        for(let i = 0; i < this.state.graphNum; i++){
            res.push(this.Item(i));
        }
        return (
            <Form>
                {res}
            </Form>
        )

    }

    ErrorToast(){

        return (
            <div
                aria-live="polite"
                aria-atomic="true"
                style={{
                    position: 'relative',
                    minHeight: '200px',
                }}
            >
                <div
                    style={{
                        position: 'absolute',
                        top: 0,
                        right: 0,
                    }}
                >
                    {this.state.serverError.error ? <Toast>
                        <Toast.Header>
                            <img src="holder.js/20x20?text=%20" className="rounded mr-2" alt="" />
                            <strong className="mr-auto">Bootstrap</strong>
                            <small>just now</small>
                        </Toast.Header>
                        <Toast.Body>{this.state.serverError.message}</Toast.Body>
                    </Toast> : ""}
                </div>
            </div>
        )
    }
    render() {
        let options = this.state.allVariables.map((v) => {
            return ({value: v, label: v})
        });
        let selected = this.state.selectedVariables.map((v) => {
            return ({value: v, label: v})
        });
        let props = [{value: "All", label: "All"}].concat(this.state.allProps.map(
            (v) => {
                //this.json.proposition_names[v]
                return ({
                    value: v,
                    label: (v + " = (" + this.json.proposition_names[v] + ")")
                });
            }));
        let selectedProps = this.state.selectedProps.map((v) => {
            return ({value: v, label: v})
        });

        // TODO: Update precision of graph after update.
        return (
            <div>
                <div className="row">
                    <this.ErrorToast/>
                    <div className="col-md-1"/>
                    <div className="col-md-10">
                        <label>Models</label>
                        <Select isSearchable={true} options={this.state.model.map(
                            (v) => {
                                return ({value: v.title, label: v.title});
                            }
                        )} onChange={this.onModelListSelect}/>
                    </div>
                    <div className="col-md-1">
                        <Button variant="outline-dark" onClick={this.onResetButtonClick} id="non-outline">reset</Button>
                    </div>
                </div>

                {this.json.isEmpty() ?
                    (
                        <div>
                            <div className="row basic_box">
                                <div className="col-md-12">
                                    <div className="row">
                                        <div className="col-md-1"/>
                                        <div className="col-md-10">
                                            <label>Variables</label>
                                            <Select className="select_theme" options={options}
                                                    onChange={this.onVariablesChange}
                                                    value={selected}
                                                    isMulti={true} isSearchable={true}
                                                    closeMenuOnSelect={false}>
                                            </Select>
                                        </div>
                                        <div className="col-md-1"/>
                                    </div>

                                    <div className="row line_plot_container">
                                        <div className="col-md-1"/>
                                        <div className="col-md-10">
                                            <label>Propositions</label>
                                            <Select isSearchable={true} options={props}
                                                    onChange={this.onPropSelect}
                                                    value={selectedProps}
                                                    isMulti={true}
                                                    closeMenuOnSelect={false}/>
                                        </div>
                                        <div className="col-md-1"/>
                                    </div>

                                    <div className="row basic_box">
                                        <div className="col-md-1"/>
                                        <div className="col-md-7"/>
                                        <div className="col-md-4">
                                            <div className="form-check text-right">
                                                <label>Enabled Popups &nbsp;
                                                    <input className="form-check-input" type="checkbox"
                                                           checked={this.state.popup.isEnabled} onClick={this.onPopupClick}
                                                           onChange={this.onPopupChange}/>
                                                </label>
                                            </div>
                                        </div>
                                    </div>

                                    <this.ItemList/>
                                    {/*<div className="row">*/}
                                    {/*    {}*/}
                                    {/*    /!*<div className="svg_div" id="graph">*!/*/}
                                    {/*    /!*    <span></span>*!/*/}
                                    {/*    /!*</div>*!/*/}
                                    {/*</div>*/}

                                </div>
                            </div>


                        </div>
                    )
                    : (
                        <div className="row line_plot_div">
                            <div className="col-md-1"/>
                            <div className="col-md-10 alert alert-warning" role="alert">
                                Nothing to show!
                            </div>
                            <div className="col-md-1"/>
                        </div>
                    )}
            </div>);
    }
}

export default LinePlot;