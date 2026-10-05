import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_26 :
    (List.ofFn coreChunks509_26).flatten =
      (coreData509.take (coreResources509 26).q).drop 118 := by
  decide +kernel

theorem coreCheck509_26 :
    ∀ c : Fin 1, (coreChunks509_26 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 26)) = true := by
  decide +kernel
#print axioms coreFlatten509_26
#print axioms coreCheck509_26
end Erdos883Verified
