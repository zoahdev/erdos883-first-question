import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_2 :
    (List.ofFn coreChunks31_2).flatten =
      (coreData31.take (coreResources31 2).q).drop 6 := by
  decide +kernel

theorem coreCheck31_2 :
    ∀ c : Fin 1, (coreChunks31_2 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 2)) = true := by
  decide +kernel
#print axioms coreFlatten31_2
#print axioms coreCheck31_2
end Erdos883Verified
