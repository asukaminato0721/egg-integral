import os
import pathlib
import re
from typing import List

FILTER = {
    "With",
    "RemoveContent",
    "Subst",
    "Coefficient",
    "LinearQ",
    "ExpandIntegrand",
    "ExpandTrigReduce",
    "ExpandToSum",
    "Unintegrable",
    "CannotIntegrate",
    "PolyGCD",
    "NormalizePseudoBinomial",
    "SimplerQ",
    "ExpandTrig",
    "SimplifyIntegrand",
    "Block",
    "Coeff",
    "PolynomialQuotient",
    "RationalFunctionQ",
    "ExpandLinearProduct",
    "PolynomialDivide",
    "ActivateTrig",
    "IntHide",
    "Dist",
    "PolyQ",
    "MatchQ",
    "QuotientOfLinearsParts",
    "LeafCount",
    "IntBinomialQ",
    "AlgebraicFunctionQ",
    "BinomialQ",
    "SimplerSqrtQ",
    "NiceSqrtQ",
    "HalfIntegerQ",
    "RationalQ",  # need to allow, no idea
    'ComplexFreeQ',
    'TrigQ',
    'TrigSimplifyQ',
    'HyperbolicQ',
    # may be allow?
    "Hypergeometric",
    "Integral",
    "ProductLog",
    "Bessel",
    "Fresnel",
    "PolyLog",
    "PolyGamma",
    "Zeta",
    "Erf",
    "Elliptic",
    "AppellF1",
    "Rt",
    # temp remove, let it work first
    "LtQ",
    "LeQ",
    'IGeQ',
    'EqQ',
    "Gamma",
    "IntPart",
    "FracPart",
    "ArcTanh",
    "csc",
    "Sinh",
    "Cosh",
    "ArcSech",
    "ArcCsch",
    "ArcCsc",
    "ArcSec",
    "Derivative",
    "Simp",
    "ArcCot",
    "ArcCoth",
    "sec",
    "Sec",
    "Csc",
    "Cot",
    "cot",
    "Tanh",
    "tanh",
    "Complex",
    "f'" # Derivative
}

index = 0


def process_m_files(directory: str):
    global index
    """
    Walks through a directory, processes .m files,
    and writes lines without "Log" to new files.

    Args:
      directory: The directory to process.
    """
    collected: List[str] = []
    for path in pathlib.Path(directory).rglob("*.m"):
        for i in path.open("r").readlines():
            i = i.strip()
            if (
                i
                and i.startswith("Int")
                and ":=" in i
                and not i.endswith(":=")
                and all(x not in i for x in FILTER)
                and "Map[Function[Int" not in i
                and "Stats | Step | Steps" not in i
            ):
                i = re.sub(r"\(\*(.*?)\*\)", " ", i)  # remove comment
                i = (
                    i.replace("_Symbol", "").replace("_.", "").replace("_", "")
                )  # make it easier
                i = i.replace("FreeQ", "freeq").replace(
                    "IntegerQ", "integerQ"
                )  # avoid calculate
                if "/;" not in i:
                    left, right = i.split(":=")
                    collected.append(f"{{ {index}, {left}, {right} }}")
                    index += 1
                    continue
                assert "/;" in i
                left, middle_right = i.split(":=")
                middle, right = middle_right.split("/;")
                collected.append(f"{{ {index}, {left}, {middle}, {right}}}")
                index += 1
    return collected


if __name__ == "__main__":
    directory_to_process = "../Rubi"  # Replace with your directory
    print(
        *process_m_files(directory_to_process),
        sep="\n",
        file=pathlib.Path("./rules.wls").open("w"),
    )
    os.system("wolframscript -f gen.wls > rule.egg")
