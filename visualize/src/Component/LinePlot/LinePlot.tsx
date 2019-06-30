import React from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import { Line } from '../Core/graph';
import { size, margin } from '../Core/Util/util';
//import { Renderer } from '../Visualize/Visualize';
import {Renderer} from '../Comb/Visualize/Visualize';
import {Json} from '../Visualize/Visualize';
import Select from 'react-select';
import { ValueType, ActionMeta } from 'react-select/src/types';
import SelectComponent from '../Select/Select'
/*

 * Props and State
 */ 
interface Props {
    jsonpath: string;
    files: {
        category: string;
        dir: string;
        title: string;
    }[];
}

interface Popup{
    isEnabled: boolean;
}

interface State {
    data: string;
    popup: Popup;
    selectFile: { value: string; label: string;}[];
    props: string[];
    value: {
        category: string;
        dir: string;
        title: string;
    };
}

/*
 * LinePlot Component
 * no longer need constructors
 * https://medium.com/@martin_hotell/react-typescript-and-defaultprops-dilemma-ca7f81c661c7
 */
class LinePlot extends React.Component<Props, State> {
    
    private width:number = parseFloat(styleVariable.width.replace("px", ""));
    private height:number = parseFloat(styleVariable.height.replace("px", ""));
    private width_viewer:number = parseFloat(styleVariable.width_viewer.replace("px", ""));
    private height_viewer:number = parseFloat(styleVariable.height_viewer.replace("px", ""));
    private width_controller:number = parseFloat(styleVariable.width_controller.replace("px", ""));
    private height_controller:number = parseFloat(styleVariable.height_controller.replace("px", ""));

    private margin_viewer_top:number = parseFloat(styleVariable.margin_viewer_top.replace("px",""));
    private margin_viewer_right:number = parseFloat(styleVariable.margin_viewer_right.replace("px",""));
    private margin_viewer_bottom:number = parseFloat(styleVariable.margin_viewer_bottom.replace("px",""));
    private margin_viewer_left:number = parseFloat(styleVariable.margin_viewer_left.replace("px",""));

    private margin_controller_top:number = parseFloat(styleVariable.margin_controller_top.replace("px",""));
    private margin_controller_right:number = parseFloat(styleVariable.margin_controller_right.replace("px",""));
    private margin_controller_bottom:number = parseFloat(styleVariable.margin_controller_bottom.replace("px",""));
    private margin_controller_left:number = parseFloat(styleVariable.margin_controller_left.replace("px",""));

    private options = [
        { value: 'chocolate', label: 'Chocolate' },
        { value: 'strawberry', label: 'Strawberry' },
        { value: 'vanilla', label: 'Vanilla' },
      ];
    private renderer:Renderer = new Renderer(
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
        "."+lineplotStyle.main_theme
    );

    private line:Line = new Line(
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
        "."+lineplotStyle.main_theme);

    // default props
    static defaultProps:Props = {
        jsonpath: '../../DataDir/test.json',
        files:[{
            category: "railroad",
            dir: "../../DataDir/railRoadPoly_1.json",
            title: "railRoadPoly_1"
        },{
            category: "railroad",
            dir: "../../DataDir/railRoadPoly_2.json",
            title: "railRoadPoly_2"
        },{
            category: "railroad",
            dir: "../../DataDir/railRoadPoly_3.json",
            title: "railRoadPoly_3"
        },{
            category: "twobattery",
            dir: "../../DataDir/twoBatteryPoly_1.json",
            title: "twoBatteryPoly_1"
        },{
            category: "twobattery",
            dir: "../../DataDir/twoBatteryPoly_2.json",
            title: "twoBatteryPoly_2"
        },{
            category: "twobattery",
            dir: "../../DataDir/twoBatteryPoly_3.json",
            title: "twoBatteryPoly_3"
        },{
            category: "twobattery",
            dir: "../../DataDir/twoBatteryPoly_4.json",
            title: "twoBatteryPoly_4"
        },{
            category: "twothermostat",
            dir: "../../DataDir/twoThermostatPoly_1.json",
            title: "twoThermostatPoly_1"
        },{
            category: "twothermostat",
            dir: "../../DataDir/twoThermostatPoly_2.json",
            title: "twoThermostatPoly_2"
        },{
            category: "twothermostat",
            dir: "../../DataDir/twoThermostatPoly_3.json",
            title: "twoThermostatPoly_3"
        },{
            category: "twothermostat",
            dir: "../../DataDir/twoThermostatPoly_4.json",
            title: "twoThermostatPoly_4"
        },{
            category: "twowatertank",
            dir: "../../DataDir/twoWatertankPoly_1.json",
            title: "twoWatertankPoly_1"
        },{
            category: "twowatertank",
            dir: "../../DataDir/twoWatertankPoly_2.json",
            title: "twoWatertankPoly_2"
        },{
            category: "twowatertank",
            dir: "../../DataDir/twoWatertankPoly_3.json",
            title: "twoWatertankPoly_3"
        }]
    }

    private json = new Json(require('../../DataDir/railRoadPoly_1.json'));

    // this will get error if change './data/test.json' to this.props.jsonpath
    state:State = {
        data: require('../../DataDir/railRoadPoly_1.json'),
        popup: {
            isEnabled: true,
        },
        selectFile: [],
        props: [],
        value: {
            category: "",
            dir: "",
            title: ""
        }
    }

    private myRef:React.RefObject<SelectComponent>
    private selectedVariables:{ value: string; label: string;}[] = [];
    constructor(props:Props){
        super(props)
        this.onPopupChange = this.onPopupChange.bind(this)
        this.onPopupClick = this.onPopupClick.bind(this)
        this.onPropSelect = this.onPropSelect.bind(this)
        this.onPropListSelect = this.onPropListSelect.bind(this)
        this.onVariableChange = this.onVariableChange.bind(this)
        
        this.json.parse();
         // first name
        // if there is not any error..........
        this.renderer.updateProp(this.json.propNames[0]);
        this.myRef = React.createRef();
    }


    componentDidMount(){
        // must invoke setdata() before draw()
        //console.log("componentDidMount");
        //this.json.parse();
        this.renderer.setdata(this.json);
        this.renderer.selectedVariables = this.json.names;
        console.log(this.renderer.selectedVariables)
        //console.log(this.renderer.getPropList())
        if(!this.json.isEmpty()){
            this.renderer.setCanvas();
            this.renderer.draw();
        }
       
        //this.line.setdata(this.state.data);
        //this.line.draw();
    }

    onPopupChange(e: React.ChangeEvent<HTMLInputElement>){
    }

    onPopupClick(e: React.MouseEvent<HTMLInputElement, MouseEvent>){
        this.setState({
            popup: {
                isEnabled: e.currentTarget.checked
            }
        }, ()=>{ this.renderer.updatePopup(this.state.popup.isEnabled) })
        console.log("mouse event")
        console.log(this.state)
    }

    onPropSelect(e: React.ChangeEvent<HTMLSelectElement>){
        //console.log("propselect: "+e.target.value);
        this.renderer.redrawPropCanvas(e.target.value)
    }

    onPropListSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta){
        //console.log("propListselect: "+e.target.value);
        //console.log("propListSelect: "+(value2 as { value: string; label: string; })["value"])
        //let tmp_json = new Json(require("../../DataDir/"+(value2 as { value: string; label: string; })["value"]+".json"));
        //tmp_json.parse();
        this.json.string = require("../../DataDir/"+(value2 as { value: string; label: string; })["value"]+".json");
        this.renderer.setdata(this.json);
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0]);

        let names = this.json.names.map(
            (v)=>{
                return {value: v, label:v}
            })
        this.setState({selectFile: names})

        if(this.myRef.current){
            this.myRef.current!.handleChange(names);
        }
        this.forceUpdate();
    }

    onVariableChange(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta){
        console.log("hello")
        console.log((value2 as ({ value: string; label: string; }[])));
        let tmp:string[] = []
        for(let el of (value2 as { value: string; label: string; }[])){
            tmp.push(el["value"])
        }
        this.renderer.selectedVariables = tmp;
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0]);
        //this.selectedVariables = (value2 as { value: string; label: string; }[])
    }

    render() {
        /*this.setState({
            props: this.renderer.getPropList()
        });*/    
        const { data, popup, selectFile, props, value} = this.state
        
        return (
        <div id="graph" className={lineplotStyle.main_theme}>
            <div className="form-group">
                <label>Models</label>
                    <Select isSearchable={true} options={this.props.files.map(
                            (v)=>{
                                return ({ value: v.title, label: v.title });
                            }
                        )} onChange={this.onPropListSelect}/>                
            </div>
            {!this.json.isEmpty() ?
            (<div className="row">
                <div className="col-md-4">
                    <div className="form-check">
                        <label>Enabled Popups &nbsp;
                            <input className="form-check-input" type="checkbox" checked={this.state.popup.isEnabled} onClick={this.onPopupClick} onChange={this.onPopupChange}/>
                        </label>
                    </div>
                </div>

                <div className="col-md-6">
                    <div className="form-group">
                        <label>Variables</label>
                            <Select className="select_theme" options={selectFile} onChange={this.onVariableChange} defaultValue={selectFile} isMulti={true} isSearchable={true} closeMenuOnSelect={false}>
                            </Select>
                        
                    </div>
                </div>
                
                <div className="col-md-2">
                    <div className="form-group">
                        <label>Propositions
                            <select className="form-control" id="exampleFormControlSelect1" onChange={this.onPropSelect}>
                                {this.json.propNames.map(
                                    (v, i)=>{
                                        return (<option key={i}>{v}</option>);
                                    }
                                )}
                            </select>
                        </label>
                    </div>
                </div>
    
            </div>) 
            : (
                <div className="alert alert-warning" role="alert">
                    Nothing to show!
                </div>
            )}
        </div>);
    }
}

export default LinePlot;