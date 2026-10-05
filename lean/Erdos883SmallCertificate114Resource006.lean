import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_6 :
    (List.ofFn coreChunks114_6).flatten =
      (coreData114.take (coreResources114 6).q).drop 24 := by
  decide +kernel

theorem coreCheck114_6 :
    ∀ c : Fin 1, (coreChunks114_6 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 6)) = true := by
  decide +kernel
#print axioms coreFlatten114_6
#print axioms coreCheck114_6
end Erdos883Verified
