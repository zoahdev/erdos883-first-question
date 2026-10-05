import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_78 :
    (List.ofFn coreChunks509_78).flatten =
      (coreData509.take (coreResources509 78).q).drop 153 := by
  decide +kernel

theorem coreCheck509_78 :
    ∀ c : Fin 1, (coreChunks509_78 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 78)) = true := by
  decide +kernel
#print axioms coreFlatten509_78
#print axioms coreCheck509_78
end Erdos883Verified
