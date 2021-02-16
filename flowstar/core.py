import os
import asyncio
import shutil
import random

from stlmcPy.util.logger import Logger


class FlowStar:
    def __init__(self):
        self.result = None
        self.logger = Logger()

    def _check_if_string_in_file(self, file_name, string_to_search):
        """ Check if any line in the file contains given string """
        # Open the file in read only mode
        with open(file_name, 'r') as read_obj:
            # Read all lines in the file one by one
            for line in read_obj:
                # For each line, check if line contains the string
                if string_to_search in line:
                    return True
        return False

    async def _run_command(self, model_string):
        model_file = "./fs_model{}.model".format(random.random())

        outputs = "./outputs"
        images = "./images"
        counterexamples = "./counterexamples"

        f = open(model_file, 'w')
        f.write(model_string)
        f.close()

        proc = await asyncio.create_subprocess_exec(
            './flowstar/flowstar', model_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)

        self.logger.start_timer("solving timer")
        stdout, stderr = await proc.communicate()
        self.logger.stop_timer("solving timer")
        #print(f'[exited with {proc.returncode}]')
        #if stdout:
        #    print(f'[stdout]\n{stdout.decode()}')
        #if stderr:
        #    print(f'[stderr]\n{stderr.decode()}')

        if os.path.isdir(outputs):
            shutil.rmtree(outputs)

        if os.path.isdir(counterexamples):
            shutil.rmtree(counterexamples)

        if os.path.isdir(images):
            shutil.rmtree(images)

        if os.path.isfile(model_file):
            os.remove(model_file)

        if "UNSAFE" in stdout.decode():
            self.result = True
        else:
            self.result = False
        # if os.path.isfile(result_file):
        #     self.result = self._check_if_string_in_file(result_file, "error")

        return stdout.decode().strip()

    async def _run(self, model_string):
        try:
            await asyncio.wait_for(self._run_command(model_string), timeout=10000.0)
        except asyncio.TimeoutError:
            print('timeout!')

    def run(self, model_string):
        asyncio.run(self._run(model_string))
