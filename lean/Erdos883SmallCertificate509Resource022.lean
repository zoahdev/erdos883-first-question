import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_22 :
    (List.ofFn coreChunks509_22).flatten =
      (coreData509.take (coreResources509 22).q).drop 112 := by
  decide +kernel

theorem coreCheck509_22 :
    ∀ c : Fin 1, (coreChunks509_22 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 22)) = true := by
  decide +kernel
#print axioms coreFlatten509_22
#print axioms coreCheck509_22
end Erdos883Verified
