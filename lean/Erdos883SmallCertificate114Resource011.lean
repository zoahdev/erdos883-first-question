import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_11 :
    (List.ofFn coreChunks114_11).flatten =
      (coreData114.take (coreResources114 11).q).drop 31 := by
  decide +kernel

theorem coreCheck114_11 :
    ∀ c : Fin 1, (coreChunks114_11 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 11)) = true := by
  decide +kernel
#print axioms coreFlatten114_11
#print axioms coreCheck114_11
end Erdos883Verified
