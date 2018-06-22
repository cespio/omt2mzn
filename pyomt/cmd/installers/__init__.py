# Copyright 2014 Andrea Micheli and Marco Gario
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from pyomt.cmd.installers.msat import MSatInstaller
from pyomt.cmd.installers.z3 import Z3Installer
from pyomt.cmd.installers.cvc4 import CVC4Installer
from pyomt.cmd.installers.yices import YicesInstaller
from pyomt.cmd.installers.btor import BtorInstaller
from pyomt.cmd.installers.pico import PicoSATInstaller
from pyomt.cmd.installers.bdd import CuddInstaller

assert MSatInstaller and Z3Installer and CVC4Installer and YicesInstaller
assert BtorInstaller and PicoSATInstaller and CuddInstaller
