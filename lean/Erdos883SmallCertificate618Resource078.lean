import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_78 :
    (List.ofFn coreChunks618_78).flatten =
      (coreData618.take (coreResources618 78).q).drop 154 := by
  decide +kernel

theorem coreCheck618_78 :
    ∀ c : Fin 1, (coreChunks618_78 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 78)) = true := by
  decide +kernel
#print axioms coreFlatten618_78
#print axioms coreCheck618_78
end Erdos883Verified
