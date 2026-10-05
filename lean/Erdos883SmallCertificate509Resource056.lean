import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_56 :
    (List.ofFn coreChunks509_56).flatten =
      (coreData509.take (coreResources509 56).q).drop 105 := by
  decide +kernel

theorem coreCheck509_56 :
    ∀ c : Fin 1, (coreChunks509_56 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 56)) = true := by
  decide +kernel
#print axioms coreFlatten509_56
#print axioms coreCheck509_56
end Erdos883Verified
