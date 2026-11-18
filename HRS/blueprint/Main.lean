import VersoManual
import VersoBlueprint.PreviewManifest
import Contents
open Verso Doc
open Verso.Genre Manual
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData (%doc Contents) args (extensionImpls := by exact extension_impls%) (config := { htmlDepth := 1 })
