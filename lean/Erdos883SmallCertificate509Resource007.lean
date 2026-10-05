import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_7 :
    (List.ofFn coreChunks509_7).flatten =
      (coreData509.take (coreResources509 7).q).drop 70 := by
  decide +kernel

theorem coreCheck509_7 :
    ∀ c : Fin 2, (coreChunks509_7 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 7)) = true := by
  decide +kernel
#print axioms coreFlatten509_7
#print axioms coreCheck509_7
end Erdos883Verified
