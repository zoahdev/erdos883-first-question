import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_65 :
    (List.ofFn coreChunks509_65).flatten =
      (coreData509.take (coreResources509 65).q).drop 119 := by
  decide +kernel

theorem coreCheck509_65 :
    ∀ c : Fin 1, (coreChunks509_65 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 65)) = true := by
  decide +kernel
#print axioms coreFlatten509_65
#print axioms coreCheck509_65
end Erdos883Verified
