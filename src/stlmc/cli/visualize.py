from __future__ import annotations

import os
import argparse

def tuple_type(strings):
    strings = strings.replace("(", "").replace(")", "").replace(" ", "")
    splits = strings.split(",")
    remove_redundant = set()
    for s in splits:
        if s != "":
            remove_redundant.add(s)
    return remove_redundant


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('file', nargs='?', type=str, help="target counterexample data file")
    parser.add_argument('-cfg', metavar='C', type=str,
                        help="set a visualization configuration file (default: \'<file>.cfg\')")
    parser.add_argument("-output", metavar="O", nargs='?', type=str,
                        help="set output format, one of {html, pdf, text} (default: html)")
    args = parser.parse_args()

    try:
        if args.file is None:
            raise ValueError("should provide a counterexample data file")

        if not os.path.exists(args.file):
            raise ValueError("\'{}\' does not exist".format(args.file))

        if os.path.isdir(args.file):
            raise ValueError("\'{}\' is not a file".format(args.file))

        from ..artifacts.codec import load_artifact
        data = load_artifact(args.file)

        # Visualization dependencies are intentionally loaded after argparse,
        # so `stlmc-vis -h` does not initialize Bokeh, Lark, or STLmc solvers.
        from ..parser.visualize_visitor import VisualizeConfigParser
        from ..visualize.visualizer import Visualizer

        file_name = os.path.basename(args.file).split(".")[0]

        supported_outputs = ["html", "pdf", "text"]

        core_data = data[:9]
        init = data[9] if len(data) > 9 else None
        const_dict = data[10] if len(data) > 10 else None

        if args.output is not None and args.output not in supported_outputs:
            raise ValueError(
                "STLmc visualization script does not support output format {}".format(args.output)
            )

        if args.output == "text":
            visualizer = Visualizer()
            visualizer.write_text(args.file, *core_data, init, const_dict)
            return

        if args.cfg is None:
            args.cfg = "{}.cfg".format(file_name)

        if not os.path.exists(args.cfg):
            raise ValueError("\'{}\' does not exist".format(args.cfg))

        if os.path.isdir(args.cfg):
            raise ValueError("\'{}\' is not a file".format(args.cfg))

        print("read configuration file \'{}\' ... ".format(args.cfg))
        config_parser = VisualizeConfigParser()
        config_parser.read(args.cfg)

        output = config_parser.output
        if args.output:
            output = args.output

        visualizer = Visualizer()
        if output == "html":
            visualizer.generate_plot(*core_data, config_parser.group)
            visualizer.write("{}".format(args.file))

        elif output == "pdf":
            from ..visualize.pdf import require_matplotlib, write_pdf
            require_matplotlib()
            point_samples, robustness_dict, time_samples_list, formula_id_dict, formula_label, delta = visualizer.generate_data(*core_data)
            write_pdf(file_name, config_parser.group, formula_id_dict, point_samples, robustness_dict, time_samples_list, delta, formula_label)

        elif output == "text":
            visualizer.write_text(args.file, *core_data, init, const_dict)

        else:
            if args.output == "" or args.output is None:
                raise ValueError("output format should be given ([pdf, html, text])")
            else:
                raise ValueError("STLmc visualization script dose not support output format {}".format(args.output))
    except ValueError as err:
        print("visualization error: {}".format(err))
        return 2
