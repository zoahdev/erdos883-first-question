import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_21 :
    (List.ofFn coreChunks509_21).flatten =
      (coreData509.take (coreResources509 21).q).drop 111 := by
  decide +kernel

theorem coreCheck509_21 :
    ∀ c : Fin 1, (coreChunks509_21 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 21)) = true := by
  decide +kernel
#print axioms coreFlatten509_21
#print axioms coreCheck509_21
end Erdos883Verified
