import Erdos883AdaptiveSpan25027Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_8 : adaptiveNumericSpans25027_8.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_8 : adaptiveSpanEven25027_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_8 : adaptiveSpanEven25027_8.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_8 : adaptiveSpanEven25027_8.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_8 : adaptiveSpanWhole25027_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_8 : adaptiveSpanWhole25027_8.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_8 : adaptiveSpanWhole25027_8.spans = coreWholeSpans 0 adaptiveNumericSpans25027_8 := by
  decide +kernel
end Erdos883Verified
