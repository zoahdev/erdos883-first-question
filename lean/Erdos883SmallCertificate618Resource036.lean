import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_36 :
    (List.ofFn coreChunks618_36).flatten =
      (coreData618.take (coreResources618 36).q).drop 154 := by
  decide +kernel

theorem coreCheck618_36 :
    ∀ c : Fin 1, (coreChunks618_36 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 36)) = true := by
  decide +kernel
#print axioms coreFlatten618_36
#print axioms coreCheck618_36
end Erdos883Verified
