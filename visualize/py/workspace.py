import os
import sys

path_dir="../src/DataDir/"
file_list = os.listdir(path_dir)
print(file_list)
workspace_info = dict()

workspace_info["file_list"] = file_list

import json
f = open((path_dir+".workspace_info.json"), "w")
json.dump(workspace_info, f)
f.close()

print("Workspace update done")
sys.stdout.flush()