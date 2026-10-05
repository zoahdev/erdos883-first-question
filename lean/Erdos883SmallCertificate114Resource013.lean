import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_13 :
    (List.ofFn coreChunks114_13).flatten =
      (coreData114.take (coreResources114 13).q).drop 34 := by
  decide +kernel

theorem coreCheck114_13 :
    ∀ c : Fin 1, (coreChunks114_13 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 13)) = true := by
  decide +kernel
#print axioms coreFlatten114_13
#print axioms coreCheck114_13
end Erdos883Verified
