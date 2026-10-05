import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_59 :
    (List.ofFn coreChunks509_59).flatten =
      (coreData509.take (coreResources509 59).q).drop 109 := by
  decide +kernel

theorem coreCheck509_59 :
    ∀ c : Fin 1, (coreChunks509_59 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 59)) = true := by
  decide +kernel
#print axioms coreFlatten509_59
#print axioms coreCheck509_59
end Erdos883Verified
