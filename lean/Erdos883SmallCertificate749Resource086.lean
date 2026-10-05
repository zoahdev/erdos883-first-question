import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_86 :
    (List.ofFn coreChunks749_86).flatten =
      (coreData749.take (coreResources749 86).q).drop 151 := by
  decide +kernel

theorem coreCheck749_86 :
    ∀ c : Fin 1, (coreChunks749_86 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 86)) = true := by
  decide +kernel
#print axioms coreFlatten749_86
#print axioms coreCheck749_86
end Erdos883Verified
