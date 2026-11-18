import HeadlineContents
import VersoManual
import VersoBlueprint.PreviewManifest
open Verso Doc
open Verso.Genre Manual
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData (%doc HeadlineContents) args
    (extensionImpls := by exact extension_impls%) (config := { htmlDepth := 1 })
