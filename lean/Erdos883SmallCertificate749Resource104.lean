import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_104 :
    (List.ofFn coreChunks749_104).flatten =
      (coreData749.take (coreResources749 104).q).drop 186 := by
  decide +kernel

theorem coreCheck749_104 :
    ∀ c : Fin 1, (coreChunks749_104 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 104)) = true := by
  decide +kernel
#print axioms coreFlatten749_104
#print axioms coreCheck749_104
end Erdos883Verified
