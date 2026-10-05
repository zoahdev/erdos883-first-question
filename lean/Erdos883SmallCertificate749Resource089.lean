import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_89 :
    (List.ofFn coreChunks749_89).flatten =
      (coreData749.take (coreResources749 89).q).drop 157 := by
  decide +kernel

theorem coreCheck749_89 :
    ∀ c : Fin 1, (coreChunks749_89 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 89)) = true := by
  decide +kernel
#print axioms coreFlatten749_89
#print axioms coreCheck749_89
end Erdos883Verified
