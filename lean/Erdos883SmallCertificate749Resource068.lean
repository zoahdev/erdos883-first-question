import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_68 :
    (List.ofFn coreChunks749_68).flatten =
      (coreData749.take (coreResources749 68).q).drop 128 := by
  decide +kernel

theorem coreCheck749_68 :
    ∀ c : Fin 1, (coreChunks749_68 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 68)) = true := by
  decide +kernel
#print axioms coreFlatten749_68
#print axioms coreCheck749_68
end Erdos883Verified
