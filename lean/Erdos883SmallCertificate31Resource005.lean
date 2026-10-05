import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_5 :
    (List.ofFn coreChunks31_5).flatten =
      (coreData31.take (coreResources31 5).q).drop 9 := by
  decide +kernel

theorem coreCheck31_5 :
    ∀ c : Fin 1, (coreChunks31_5 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 5)) = true := by
  decide +kernel
#print axioms coreFlatten31_5
#print axioms coreCheck31_5
end Erdos883Verified
