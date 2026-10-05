import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_11 :
    (List.ofFn coreChunks509_11).flatten =
      (coreData509.take (coreResources509 11).q).drop 100 := by
  decide +kernel

theorem coreCheck509_11 :
    ∀ c : Fin 1, (coreChunks509_11 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 11)) = true := by
  decide +kernel
#print axioms coreFlatten509_11
#print axioms coreCheck509_11
end Erdos883Verified
