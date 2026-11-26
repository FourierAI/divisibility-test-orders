"""Compile the native word port against the verified PyPI witness tables."""
import hashlib
import io
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

if len(sys.argv) != 3:
    sys.exit("usage: build_berg.py miller_rabin-1.0.1.tar.gz output.dylib")
archive = Path(sys.argv[1]).read_bytes()
digest = hashlib.sha256(archive).hexdigest()
if digest != "0ba0ab6cddb4ee6f9bdf829b66b7bb8e363ce5fdb80241528e461c667816a926":
    sys.exit("unrecognized source distribution")
with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as data:
    def read(name):
        return data.extractfile("miller_rabin-1.0.1/" + name).read().decode()
    source = read("src/miller_rabin.c")
    notices = "\n".join(read(f) for f in ("COPYING","COPYING.techneon","COPYING.boost"))
start = source.index("static const uint32_t smallprime16[]")
stop = source.index("static bool\npreliminary_test(mpz_t")
with tempfile.TemporaryDirectory() as tmp:
    Path(tmp,"berg_tables.h").write_text("/*\n"+notices+"\n*/\n"+source[start:stop])
    subprocess.run(["clang++","-std=c++17","-O3","-mcpu=native","-dynamiclib",
                    "-I",tmp,str(Path(__file__).with_name("berg.cpp")),
                    "-o",sys.argv[2]],check=True)
