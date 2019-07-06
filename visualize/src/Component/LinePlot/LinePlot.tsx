import React from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import {margin, size} from '../Core/Util/Util';
import {Renderer} from '../Renderer/MainRenderer';
import {Json, WorkspaceJson} from '../Core/Util/DataParser';
import Select from 'react-select';
import {ActionMeta, ValueType} from 'react-select/src/types';

/*

 * Props and State
 */
interface Props {
}

interface Popup {
    isEnabled: boolean;
}

interface State {
    data: string;
    popup: Popup;
    selectFile: { value: string; label: string; }[];
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
        "." + lineplotStyle.main_theme
    );

    private json = new Json(require('../../DataDir/twoBatteryLinear_([]_(0.0,20.5)^[0.0,inf) (___[3.0,14.0]^[0.0,inf) reachability))_20.json'));
    private workspace_info = new WorkspaceJson(require('../../DataDir/.workspace_info.json'));

    // this will get error if change './data/test.json' to this.props.jsonpath
    state: State = {
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
    };
    private selectedVariables: { value: string; label: string; }[] = [];

    constructor(props: Props) {
        super(props);
        this.onPopupChange = this.onPopupChange.bind(this);
        this.onPopupClick = this.onPopupClick.bind(this);
        this.onPropSelect = this.onPropSelect.bind(this);
        this.onPropListSelect = this.onPropListSelect.bind(this);
        this.onVariableChange = this.onVariableChange.bind(this);

        this.json.parse();
        // first name
        // if there is not any error..........
        this.renderer.updateProp(this.json.propNames[0]);

    }


    componentDidMount() {
        // must invoke setdata() before draw()
        //console.log("componentDidMount");
        //this.json.parse();
        this.renderer.setdata(this.json);
        this.renderer.selectedVariables = this.json.names;
        console.log(this.renderer.selectedVariables)
        //console.log(this.renderer.getPropList())
        if (!this.json.isEmpty()) {
            this.renderer.setCanvas();
            this.renderer.draw();
        }

        //this.line.setdata(this.state.data);
        //this.line.draw();
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
        })
        console.log("mouse event");
        console.log(this.state)
    }


    /* onPropSelect(e: React.ChangeEvent<HTMLSelectElement>) {
         //console.log("propselect: "+e.target.value);
         this.renderer.redrawPropCanvas(e.target.value)
     }

     */

    onPropSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {

        this.renderer.redrawPropCanvas((value2 as { value: string, label: string; })["value"]);
    }

    onPropListSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {
        //console.log("propListselect: "+e.target.value);
        //console.log("propListSelect: "+(value2 as { value: string; label: string; })["value"])
        //let tmp_json = new Json(require("../../DataDir/"+(value2 as { value: string; label: string; })["value"]+".json"));
        //tmp_json.parse();
        this.json.string = require("../../DataDir/" + (value2 as { value: string; label: string; })["value"]);
        this.renderer.setdata(this.json);
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0]);

        let names = this.json.names.map(
            (v) => {
                return {value: v, label: v}
            });
        this.setState({selectFile: names});

        this.forceUpdate();
    }

    onVariableChange(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {
        //console.log("hello")
        //console.log((value2 as ({ value: string; label: string; }[])));
        let target = (value2 as ({ value: string; label: string; }[]));
        let tmp: string[] = [];
        if (target) {
            for (let el of target) {
                tmp.push(el["value"])
            }
        }
        this.renderer.selectedVariables = tmp;
        this.renderer.reload(this.json.isEmpty(), this.json.propNames[0]);
        //this.renderer.draw()
        //this.selectedVariables = (value2 as { value: string; label: string; }[])
    }

    render() {

        return (
            <div id="graph" className={lineplotStyle.main_theme}>
                <div className="form-group">
                    <label>Models</label>
                    <Select isSearchable={true} options={this.workspace_info.file_list.map(
                        (v) => {
                            return ({value: v, label: v});
                        }
                    )} onChange={this.onPropListSelect}/>
                </div>
                {!this.json.isEmpty() ?
                    (<div>
                            <div className="row">
                                <div className="col-md-4">
                                    <div className="form-check">
                                        <label>Enabled Popups &nbsp;
                                            <input className="form-check-input" type="checkbox"
                                                   checked={this.state.popup.isEnabled} onClick={this.onPopupClick}
                                                   onChange={this.onPopupChange}/>
                                        </label>
                                    </div>
                                </div>

                                <div className="col-md-6">
                                    <div className="form-group">
                                        <label>Variables</label>
                                        <Select className="select_theme" options={[]}
                                                onChange={this.onVariableChange}
                                                defaultValue={[]} isMulti={true} isSearchable={true}
                                                closeMenuOnSelect={false}>
                                        </Select>

                                    </div>
                                </div>
                            </div>
                            <div className="row">
                                <div className="form-group">
                                    <label>Propositions</label>
                                    <Select isSearchable={true} options={this.json.propNames.map(
                                        (v) => {
                                            //this.json.proposition_names[v]
                                            return ({
                                                value: v,
                                                label: (v + " = (" + this.json.proposition_names[v] + ")")
                                            });
                                        }
                                    )} onChange={this.onPropSelect}/>
                                </div>
                            </div>
                        </div>
                    )
                    : (
                        <div className="alert alert-warning" role="alert">
                            Nothing to show!
                        </div>
                    )}
            </div>);
    }
}

export default LinePlot;