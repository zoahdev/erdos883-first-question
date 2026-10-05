import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_8 :
    (List.ofFn coreChunks114_8).flatten =
      (coreData114.take (coreResources114 8).q).drop 26 := by
  decide +kernel

theorem coreCheck114_8 :
    ∀ c : Fin 1, (coreChunks114_8 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 8)) = true := by
  decide +kernel
#print axioms coreFlatten114_8
#print axioms coreCheck114_8
end Erdos883Verified
