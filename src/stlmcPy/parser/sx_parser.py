import os
import xml.etree.ElementTree as elemTree

from ..hybrid_automaton.converter.spaceex import obj2se, xml_pretty_print
from ..hybrid_automaton.hybrid_automaton import *
from ..hybrid_automaton.utils import *

from ..constraints.constraints import *
from ..constraints.aux.generator import variable
from antlr4 import InputStream, CommonTokenStream
from .model_parser import ModelParser
from .error_listener import StlmcErrorListener
from ..constraints.aux.generator import *
from ..constraints.constraints import *
from ..exception.exception import NotSupportedError
from ..syntax.spaceex.spaceexLexer import spaceexLexer
from ..syntax.spaceex.spaceexParser import spaceexParser
from ..syntax.spaceex.spaceexVisitor import spaceexVisitor

class SxParser(ModelParser, spaceexVisitor):
    def __init__(self):
        self._sx_name = "{http://www-verimag.imag.fr/xml-namespaces/sspaceex}"
        self._lower, self._upper = -999999, 999999
        self._dict = dict()
        self._cur_comp = None

    def get_parse_tree(self, file_name: str, config_name=None):
        automata_network = set()

        f, ext = os.path.splitext(file_name)

        assert ext == ".xml"
        config = "{}.cfg".format(f)

        if config_name is None:
            if not os.path.exists(config):
                raise Exception("cannot find a configuration file {}".format(config))
        else:
            config = config_name

        tree = elemTree.parse(file_name)
        root = tree.getroot()

        # print(root.tag)
        # print(root.attrib)

        for component in root:
            # component
            ty, c_attr = self._get(component)

            assert ty == "component"
            
            c_id = c_attr["id"]
            self._dict[c_id] = {"modes" : dict(), "jumps" : dict(), 
                                "const" : dict(),
                                "v_range" : dict(), "v_lookup" : dict(),
                                "v_map" : dict(), "bind" : dict()}
            
            v_d = self._dict[c_id]
            modes, jumps, v_range, v_lookup = v_d["modes"], v_d["jumps"], v_d["v_range"], v_d["v_lookup"]
            v_map, bind = v_d["v_map"], v_d["bind"]
            c_d = v_d["const"]

            #  make modes
            for child in component:
                tag, attr = self._get(child)
                # print(tag, attr)
                # variable declaration
                if tag == "param":
                    if attr["type"] == "label":
                        continue

                    v_name = attr["name"]
                    v = variable(v_name, attr["type"])

                    assert v_name not in c_d and v_name not in v_lookup

                    if attr["dynamics"] == "const":
                        c_d[attr["name"]] = v

                    elif attr["dynamics"] == "any":
                        assert v not in v_range
                        v_range[v] = Interval(True, self._lower, self._upper, True)

                        # easy to search variable by its name
                        v_lookup[attr["name"]] = v
                    else:
                        raise Exception("unsupported dynamic type ({})".format(attr["type"]))
                
                if tag == "location":
                    mode_id = attr["id"]

                    assert mode_id not in modes
                    modes[mode_id] = dict()

                    mode = modes[mode_id]

                    for c in child:
                        t, _ = self._get(c)
                        if t == "flow":
                            mode["flow"] = self._parse_sx_flow(c.text, c_id)
                        
                        if t == "invariant":
                            mode["inv"] = self._parse_sx_cond(c.text, c_id)

                if tag == "bind":
                    bind[attr["component"]] = attr["as"]
                    for c in child:
                        t, vk = self._get(c)

                        assert t == "map"

                        v_map[vk["key"]] = c.text

            # make transitions
            for child in component:
                tag, attr = self._get(child)
                if tag == "transition":
                    src, trg = attr["source"], attr["target"]

                    k = (c_id, src, trg)

                    if k not in jumps:
                        jumps[k] = list()

                    jp_s = jumps[k]
                    
                    if src not in modes:
                        raise Exception("src mode {} not found".format(src))
                    
                    if trg not in modes:
                        raise Exception("trg mode {} not found".format(trg))
                    
                    jp = dict()
                    for c in child:
                        t, _ = self._get(c)
                        if t == "guard":
                            jp["guard"] = self._parse_sx_cond(c.text, c_id)
                        
                        if t == "assignment":
                            jp["reset"] = self._parse_sx_assn(c.text, c_id)
                    
                    jp_s.append(jp)
            # print("----------")
        # print(self._dict)

    def _get(self, node: elemTree.Element):
        return node.tag.replace(self._sx_name, ""), node.attrib
    

    def _v_lookup(self, v_str: str):
        assert self._cur_comp is not None

        v_lookup = self._dict[self._cur_comp]["v_lookup"]

        if v_str not in v_lookup:
            raise Exception("a variable {} is not declared".format(v_str))

        return v_lookup[v_str]
    

    def _const_lookup(self, c_str: str):
        assert self._cur_comp is not None

        c_lookup = self._dict[self._cur_comp]["const"]

        if c_str not in c_lookup:
            raise Exception("constant {} is not declared".format(c_str))

        return c_lookup[c_str]
    

    def _parse_tree(self, sx_str: str):
        raw_model = InputStream(sx_str)
        lexer = spaceexLexer(raw_model)
        stream = CommonTokenStream(lexer)
        parser = spaceexParser(stream)
        parser.removeErrorListeners()
        model_err_listener = StlmcErrorListener()
        # model_err_listener.name = file_name
        parser.addErrorListener(model_err_listener)
        return parser


    def _parse_sx_cond(self, sx_cond: str, comp_id):
        parser = self._parse_tree(sx_cond)
        self._cur_comp = comp_id
        tree = parser.sxCond()
        cond = self.visit(tree)
        self._cur_comp = None
        return cond
    

    def _parse_sx_flow(self, sx_flow: str, comp_id):
        parser = self._parse_tree(sx_flow)
        self._cur_comp = comp_id
        tree = parser.sxFlow()
        flow = self.visit(tree)
        self._cur_comp = None
        return flow
    

    def _parse_sx_assn(self, sx_assn: str, comp_id):
        parser = self._parse_tree(sx_assn)
        self._cur_comp = comp_id
        tree = parser.sxAssn()
        assn = self.visit(tree)
        self._cur_comp = None
        return assn


    # Visit a parse tree produced by spaceexParser#sxFlow.
    def visitSxFlow(self, ctx:spaceexParser.SxFlowContext):
        return self.visitChildren(ctx)
    

    # Visit a parse tree produced by spaceexParser#sxAssn.
    def visitSxAssn(self, ctx:spaceexParser.SxAssnContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by spaceexParser#sxCond.
    def visitSxCond(self, ctx:spaceexParser.SxCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by spaceexParser#sxExpr.
    def visitSxExpr(self, ctx:spaceexParser.SxExprContext):
        print(ctx.getText())
        return self.visitChildren(ctx)

    
    # Visit a parse tree produced by spaceexParser#andFlow.
    def visitAndFlow(self, ctx:spaceexParser.AndFlowContext):
        fs1 = self.visit(ctx.flow(0))
        fs2 = self.visit(ctx.flow(1))
        return fs1.union(fs2)
    

    # Visit a parse tree produced by spaceexParser#falesFlow.
    def visitFalseFlow(self, ctx:spaceexParser.FalseFlowContext):
        return


    # Visit a parse tree produced by spaceexParser#unitFlow.
    def visitUnitFlow(self, ctx:spaceexParser.UnitFlowContext):
        v = self._v_lookup(ctx.NEXT_VAR().getText().replace("'", ""))
        e = self.visit(ctx.expr())
        return {(v, e)}


    # Visit a parse tree produced by spaceexParser#unitAssn1.
    def visitUnitAssn1(self, ctx:spaceexParser.UnitAssn1Context):
        v = self._v_lookup(ctx.NEXT_VAR().getText().replace("'", ""))
        e = self.visit(ctx.expr())
        return {(v, e)}


    # Visit a parse tree produced by spaceexParser#unitAssn2.
    def visitUnitAssn2(self, ctx:spaceexParser.UnitAssn2Context):
        v = self._v_lookup(ctx.ID().getText())
        e = self.visit(ctx.expr())
        return {(v, e)}


    # Visit a parse tree produced by spaceexParser#andAssn.
    def visitAndAssn(self, ctx:spaceexParser.AndAssnContext):
        fs1 = self.visit(ctx.assn(0))
        fs2 = self.visit(ctx.assn(1))
        return fs1.union(fs2)


    # Visit a parse tree produced by spaceexParser#varExp.
    def visitVarExp(self, ctx:spaceexParser.VarExpContext):
        try: 
            # try variable lookup
            return self._v_lookup(ctx.ID().getText())
        except Exception as e:
            # try constant lookup
            return self._const_lookup(ctx.ID().getText())


    # Visit a parse tree produced by spaceexParser#unaryFunc.
    def visitUnaryFunc(self, ctx:spaceexParser.UnaryFuncContext):
        return self.visit(ctx.expr())


    # Visit a parse tree produced by spaceexParser#parExp.
    def visitParExp(self, ctx:spaceexParser.ParExpContext):
        return self.visit(ctx.expr())


    # Visit a parse tree produced by spaceexParser#subExp.
    def visitSubExp(self, ctx:spaceexParser.SubExpContext):
        return self.visit(ctx.expr(0)) - self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#powExp.
    def visitPowExp(self, ctx:spaceexParser.PowExpContext):
        return self.visit(ctx.expr(0)) ** self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#valExp.
    def visitValExp(self, ctx:spaceexParser.ValExpContext):
        return Real(ctx.VALUE().getText())


    # Visit a parse tree produced by spaceexParser#unaryMinus.
    def visitUnaryMinus(self, ctx:spaceexParser.UnaryMinusContext):
        return - self.visit(ctx.expr())


    # Visit a parse tree produced by spaceexParser#addExp.
    def visitAddExp(self, ctx:spaceexParser.AddExpContext):
        return self.visit(ctx.expr(0)) + self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#mulExp.
    def visitMulExp(self, ctx:spaceexParser.MulExpContext):
        return self.visit(ctx.expr(0)) * self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#divExp.
    def visitDivExp(self, ctx:spaceexParser.DivExpContext):
        return self.visit(ctx.expr(0)) / self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#ltCond.
    def visitLtCond(self, ctx:spaceexParser.LtCondContext):
        return self.visit(ctx.expr(0)) < self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#parCond.
    def visitParCond(self, ctx:spaceexParser.ParCondContext):
        return self.visit(ctx.cond())


    # Visit a parse tree produced by spaceexParser#geqCond.
    def visitGeqCond(self, ctx:spaceexParser.GeqCondContext):
        return self.visit(ctx.expr(0)) >= self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#leqCond.
    def visitLeqCond(self, ctx:spaceexParser.LeqCondContext):
        return self.visit(ctx.expr(0)) <= self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#gtCond.
    def visitGtCond(self, ctx:spaceexParser.GtCondContext):
        return self.visit(ctx.expr(0)) > self.visit(ctx.expr(1))


    # Visit a parse tree produced by spaceexParser#andCond.
    def visitAndCond(self, ctx:spaceexParser.AndCondContext):
        return And([self.visit(ctx.cond(0)), self.visit(ctx.cond(1))])


    # Visit a parse tree produced by spaceexParser#eqCond.
    def visitEqCond(self, ctx:spaceexParser.EqCondContext):
        return Eq(self.visit(ctx.expr(0)), self.visit(ctx.expr(1)))


class SxWriter:
    def __init__(self):
        self._sx_name = "http://www-verimag.imag.fr/xml-namespaces/sspaceex"
        self._sx_tag = "{{{}}}".format(self._sx_name)
        self._lower, self._upper = -999999, 999999
        # self._dict = dict()
        # self._cur_comp = None

    def _get(self, node: elemTree.Element):
        return node.tag.replace(self._sx_tag, ""), node.attrib

    def add_automta(self, file_name: str, config_name: str, ha_name, ha: HybridAutomaton):
        f, ext = os.path.splitext(file_name)
        c_f, c_ext = os.path.splitext(config_name)

        assert ext == ".xml" and c_ext == ".cfg"
        # config = "{}.cfg".format(f)

        if not os.path.exists(config_name):
            raise Exception("cannot find a configuration file {}".format(config_name))

        elemTree.register_namespace('', self._sx_name)
        tree = elemTree.parse(file_name)
        root = tree.getroot()

        comp = elemTree.Element("component")
        root.insert(0, comp)

        comp.set("id", str(ha_name))
        
        v_set = get_ha_vars(ha)

        for v in v_set:
            p = elemTree.SubElement(comp, "param")
            p.set("name", v.id)
            p.set("type", v.type)
            p.set("local", "false")
            p.set("d1", "1")
            p.set("d2", "1")
            p.set("dynamics", "any")

        
        m_id_dict = dict()
        for m_id, m in enumerate(ha.get_modes()):
            m_id_dict[m] = m_id

            loc = elemTree.SubElement(comp, "location")
            loc.set("id", str(m_id))
            loc.set("name", "modeId{}".format(m_id))
            loc.set("x", "1")
            loc.set("y", "1")
            loc.set("width", "10")
            loc.set("height", "10")

            
            flows = list()
            for v in m.dynamics:
                e = m.dynamics[v]
                flows.append("{}' == {}".format(obj2se(v), obj2se(e)))
            
            flow = elemTree.SubElement(loc, "flow")
            flow.text = "&".join(flows)

            invs = list()
            for inv_f in m.invariant:
                invs.append(obj2se(inv_f))
            
            inv = elemTree.SubElement(loc, "invariant")
            inv.text = "&".join(invs)

        jp_s = get_jumps(ha)
        for jp in jp_s:
            s, t = jp.get_src(), jp.get_trg()
            s_id, t_id = m_id_dict[s], m_id_dict[t]

            tr = elemTree.SubElement(comp, "transition")
            tr.set("source", str(s_id))
            tr.set("target", str(t_id))

            g_txt = list()
            for g_f in jp.guard:
                g_txt.append(obj2se(g_f))

            g = elemTree.SubElement(tr, "guard")
            g.text = "&".join(g_txt)

            rst = list()
            for v, e in jp.reset:
                rst.append("{}' == {}".format(obj2se(v), obj2se(e)))

            r = elemTree.SubElement(tr, "assignment")
            r.text = "&".join(rst)

            lbc = elemTree.SubElement(tr, "labelposition")
            lbc.set("x", "20")
            lbc.set("y", "20")
            lbc.set("width", "20")
            lbc.set("height", "20")

        # find bind component
        bs = tree.findall("./{}component[{}bind]".format(self._sx_tag, self._sx_tag))
        if len(bs) > 1:
            raise Exception("there should be one bind component")
        
        if len(bs) == 0:
            raise Exception("no bind component found")
        
        bind = bs[0]
        bind_vars = set()
        
        ps = bind.findall("./{}param".format(self._sx_tag))
        for p in ps:
            bind_vars.add(variable(p.get("name"), p.get("type")))

        print(bind_vars)

        comp_vars: Set[Variable] = set()
        comp_attr: Dict[Variable, Dict] = dict()
        c_ps = comp.findall("./param")
        for p in c_ps:
            v = variable(p.get("name"), p.get("type"))
            
            comp_attr[v] = p.attrib
            comp_vars.add(v)

        
        p_vars = comp_vars.difference(bind_vars)
        print(p_vars)

        # add params
        for v in p_vars:
            p = elemTree.SubElement(bind, "param")
            p.attrib = comp_attr[v].copy()
        
        # add bind tag
        b = elemTree.SubElement(bind, "bind")
        b.set("component", ha_name)
        b.set("as", "{}inst".format(ha_name))
        b.set("x", "20")
        b.set("y", "20")
        for v in comp_vars:
            m = elemTree.SubElement(b, "map")
            m.set("key", v.id)
            m.text = v.id

        xml_pretty_print(root)
        tree = elemTree.ElementTree(root)
        cfg = self.mk_conf(config_name, m_id_dict, ha_name, ha)

        with open("{}-{}.xml".format(f, ha_name), "wb") as file:
            tree.write(file, encoding="utf-8", xml_declaration=True)

        with open("{}-{}.cfg".format(c_f, ha_name), "w") as file:
            file.write(cfg)

    @classmethod
    def mk_conf(cls, cfg_name : str, mode_id_dict: Dict, ha_name: str, ha: HybridAutomaton):
        f = open(cfg_name, "r")
        s = f.read()
        conf = s.split("\n")
        cfg = list()

        initial, final = list(), list()
        ha_init = [obj2se(f) for f in ha.init]

        for mode in ha.get_modes():
            assert mode in mode_id_dict
            m_id = "modeId{}".format(mode_id_dict[mode])
    
            if mode.is_initial():
                initial.append("loc({}inst) == {}".format(ha_name, m_id))
            
            if mode.is_final():
                final.append("loc({}inst) == {}".format(ha_name, m_id))

        for c in conf:
            if c[0] == "#":
                cfg.append(c)
            else:
                k, v = c.split("=", 1)
                v = v.replace("\"", "")
                if "initially" in k:
                    init = "(({}) & ({})) & ({})".format(" & ".join(ha_init), v, " || ".join(initial))
                    cfg.append("initially = \"{}\"".format(init))

                elif "forbidden" in k:
                    fin = "({}) & ({})".format(v, " || ".join(final))
                    cfg.append("forbidden = \"{}\"".format(fin))

                else:
                    cfg.append(c)

        f.close()

        return "\n".join(cfg)
