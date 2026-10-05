import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_7 :
    (List.ofFn coreChunks114_7).flatten =
      (coreData114.take (coreResources114 7).q).drop 25 := by
  decide +kernel

theorem coreCheck114_7 :
    ∀ c : Fin 1, (coreChunks114_7 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 7)) = true := by
  decide +kernel
#print axioms coreFlatten114_7
#print axioms coreCheck114_7
end Erdos883Verified
