import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_78 :
    (List.ofFn coreChunks680_78).flatten =
      (coreData680.take (coreResources680 78).q).drop 146 := by
  decide +kernel

theorem coreCheck680_78 :
    ∀ c : Fin 1, (coreChunks680_78 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 78)) = true := by
  decide +kernel
#print axioms coreFlatten680_78
#print axioms coreCheck680_78
end Erdos883Verified
