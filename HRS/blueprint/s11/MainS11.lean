import S11Contents
import VersoManual
import VersoBlueprint.PreviewManifest
open Verso Doc
open Verso.Genre Manual
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData (%doc S11Contents) args
    (extensionImpls := by exact extension_impls%) (config := { htmlDepth := 1 })
