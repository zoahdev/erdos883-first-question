import Erdos883AdaptiveSpan44342Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_8 : adaptiveNumericSpans44342_8.length = 517 := by decide +kernel
theorem adaptiveSpanEvenCache44342_8 : adaptiveSpanEven44342_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_8 : adaptiveSpanEven44342_8.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_8 : adaptiveSpanEven44342_8.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_8 : adaptiveSpanWhole44342_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_8 : adaptiveSpanWhole44342_8.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_8 : adaptiveSpanWhole44342_8.spans = coreWholeSpans 0 adaptiveNumericSpans44342_8 := by
  decide +kernel
end Erdos883Verified
