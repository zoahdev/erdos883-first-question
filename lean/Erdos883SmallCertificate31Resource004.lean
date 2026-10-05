import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_4 :
    (List.ofFn coreChunks31_4).flatten =
      (coreData31.take (coreResources31 4).q).drop 8 := by
  decide +kernel

theorem coreCheck31_4 :
    ∀ c : Fin 1, (coreChunks31_4 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 4)) = true := by
  decide +kernel
#print axioms coreFlatten31_4
#print axioms coreCheck31_4
end Erdos883Verified
