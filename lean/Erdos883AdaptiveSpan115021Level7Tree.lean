import Erdos883AdaptiveSpan115021Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_7 : adaptiveNumericSpans115021_7.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_7 : adaptiveSpanEven115021_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_7 : adaptiveSpanEven115021_7.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_7 : adaptiveSpanEven115021_7.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_7 : adaptiveSpanWhole115021_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_7 : adaptiveSpanWhole115021_7.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_7 : adaptiveSpanWhole115021_7.spans = coreWholeSpans 0 adaptiveNumericSpans115021_7 := by
  decide +kernel
end Erdos883Verified
