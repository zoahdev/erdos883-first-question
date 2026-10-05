import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_67 :
    (List.ofFn coreChunks680_67).flatten =
      (coreData680.take (coreResources680 67).q).drop 127 := by
  decide +kernel

theorem coreCheck680_67 :
    ∀ c : Fin 1, (coreChunks680_67 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 67)) = true := by
  decide +kernel
#print axioms coreFlatten680_67
#print axioms coreCheck680_67
end Erdos883Verified
